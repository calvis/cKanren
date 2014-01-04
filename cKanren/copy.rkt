#lang racket

(require cKanren/ck 
         cKanren/tree-unify 
         cKanren/neq
         cKanren/attributes
         cKanren/absento
         cKanren/src/framework
         cKanren/src/variables
         cKanren/src/operators)

(provide copyo)

;; goal that will copy the "copy" in t, i.e. the structure and
;; free variables, to x
(define (copyo t x)
  (fresh (gensym) (copy t x gensym) (copylb t x)))

;; if t is an mk-struct, copies that structure onto x.  if t is ground
;; or if there is already a (copy x t) constraint, this constraint
;; turns into ==. otherwise, placed back in the store.
(define-constraint (copy t x [sym #:constant])
  #:package (a [s c e])
  (cond
   [(and (eq? t x) (var? t))
    (add-constraint (copy t x sym))]
   [(eq? t x) succeed]
   [(occurs-check x t s) fail]
   [(pair? t)
    (fresh (first rest)
      (== x (cons first rest))
      (copy (car t) first sym)
      (copy (cdr t) rest sym))]
   [(not (var? t)) (== t x)]
   [else (add-constraint (copy t x sym))]))

(define-constraint-interaction
  [(copy x y sym) (copy x z sym)] => [(== y z) (copy x y sym)])

(define-constraint-interaction
  [(copy x y sym) (copy y z (not sym))]
  #:package (a [s c e])
  [(find-cycle z x c) [add (== x y) (== x z)]])

(define (find-cycle z x c)
  (define copys
    (filter-map (match-lambda [(list x x g) #f] [(list a d g) (cons a d)])
                (filter/rator copy c)))
  (define (loop u visted)
    (cond
     [(eq? u x) #t]
     [(memq u visted) #f]
     [(assq u copys) => (lambda (v) (loop v (cons v visted)))]
     [else #f]))
  (loop z (list)))

(define-constraint (copylb t u)
  #:reification-function
  (lambda (v r)
    (define r^ (reify-s u r))
    (reified-constraint 'copy (list t (walk* u r^)) r^))
  (cond
   [(eq? t u) succeed]
   [(pair? t)
    (fresh (first rest)
      (== u (cons first rest))
      (copylb (car t) first)
      (copylb (cdr t) rest))]
   [(not (var? t)) succeed]
   [else (add-constraint (copylb t u))]))

(define-constraint-interaction
  [(copylb t u) (copylb t u^)] 
  [(merge u u^) [(copylb t (merge u u^))]])

(define-cvar-type fvar "f")
(define (new-fvar) (fvar 'any))

(define (merge u v)
  (call/cc
   (lambda (k)
     (define/match (merger u v r)
       [((cons ua ud) (cons va vd) r)
        (define-values (u^ r^)  (merger ua va r))
        (define-values (v^ r^^) (merger ud vd r^))
        (values (cons u^ v^) r^^)]
       [(u v r) 
        (cond
         [(eq? u v) (values u r)]
         [(or (var? u) (var? v)) (k #f)]
         [(lookup u v r) => (lambda (p) (values (cddr p) r))]
         [else (values (new-fvar) (remove u v r))])])
     (define-values (u^ r) (merger u v '()))
     u^)))

(define (lookup u v r)
  (findf (match-lambda [(list a b c) (and (eq? u a) (eq? v b))]) r))

(define (remove u v r)
  (filter (match-lambda [(list a b c) (or (not (eq? u a)) (not (eq? v b)))]) r))

;; helper tests
(module+ test
  (require "tester.rkt")
  
  (test (merge 5 5) 5)
  (test (fvar? (merge 5 6)) #t)
  (test (merge `(5 ,(var 'z)) `(,(var 'z) 5)) #f))

(module+ test
  (require "tester.rkt")

  (test (run* (q) (copylb q 5)) '((_.0 : (copy (_.0 5)))))
  (test (run* (q) (copylb q 5) (copylb q 6)) '((_.0 : (copy (_.0 f.1)))))

  (test (run* (q) (copylb q q)) '(_.0))

  (test 
   (run* (x y z)
     (copylb x `(,y ,z))
     (copylb x `(,z ,y)))
   '(((_.0 _.1 _.2) : (copy (_.0 (_.1 _.2)) (_.0 (_.2 _.1))))))

  (test 
   (run* (x y z)
     (copylb x `(5 ,z))
     (copylb x `(,z 5)))
   '(((_.0 _.1 _.2) : (copy (_.0 (5 _.2)) (_.0 (_.2 5))))))

  (test 
   (run* (x y z)
     (== y 5)
     (copylb x `(,y ,z))
     (copylb x `(,z ,y)))
   '(((_.0 5 _.1) : (copy (_.0 (5 _.1)) (_.0 (_.1 5))))))

  (test 
   (run* (x y z)
     (copylb x `(,y ,z))
     (copylb x `(,z ,y))
     (== y 5))
   '(((_.0 5 _.1) : (copy (_.0 (5 _.1)) (_.0 (_.1 5)))))))

;; simple tests
(module+ test
  (test (run* (q) (copyo 5 5)) '(_.0))
  (test (run* (q) (copyo 5 q)) '(5))
  (test (run* (q) (copyo q q)) '(_.0))

  (test (run* (q) 
          (fresh (x y)
            (copyo q 5)
            (== `(,x ,y) q)))
        '())

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4 5 6 7))
            (== q 5)))
        '())

  (test (run* (q) (copyo `(,q) q)) '())

  (test (run* (x y) (copyo x `(,y)) (== x `(5)))
        '(((5) 5)))

  (test
   (run* (x y)
     (copyo `((,x) (,x)) `((,x) (,y)))) 
   '((_.0 _.0)))

  (test
   (run* (x y z)
     (copyo `(,z (,x)) `((,x) (,y)))
     (== `(,x) z))
   '((_.0 _.0 (_.0)))))

;; harder tests

(module+ test
  (test 
   (run* (q) (copyo q 5) (copyo q 6)) 
   '((_.0 : (copy (_.0 f.1)))))

  (test (run* (q)
          (fresh (x) 
            (copyo `(,x ,x) q)))
        '((_.0 _.0)))

  (test 
   (run* (x y) 
     (copyo `((,x) (,x)) y))
   '(((_.0 ((_.1) (_.1))) : (copy (_.0 _.1)))))

  (test 
   (run* (q)
     (fresh (x y) 
       (copyo `(lambda (,x) (,y ,x)) q)))
   '((lambda (_.0) (_.1 _.0))))

  (test
   (run* (x y a b)
     (== x y)
     (copyo `(,x ,y) `(,a ,b)))
   '(((_.0 _.0 _.1 _.1) : (copy (_.0 _.1)))))

  (test 
   (run* (x y a b)
     (copyo `(,x ,y) `(,a ,b))
     (== x y))
   '(((_.0 _.0 _.1 _.1) : (copy (_.0 _.1)))))

  (test 
   (run* (t t^)
     (fresh (x g g^)
       (copyo `(,t ,t) `(,t ,t^))))
   '((_.0 _.0)))
  
  (test 
   (run* (t t^)
     (fresh (g g^)
       (== `(,t) g^)
       (copyo `((,t) ,t) `(,g^ ,t^))))
   '((_.0 _.0)))

  (test 
   (run* (t t^)
     (fresh (g g^)
       (copyo `(,g ,t) `(,g^ ,t^))
       (== `(,t) g)
       (== g g^)))
   '((_.0 _.0)))

  (test 
   (run* (t t^)
     (fresh (g)
       (== `(,t) g)
       (copyo `(,g ,t) `(,g ,t^))))
   '((_.0 _.0)))

  (test 
   (run* (t t^)
     (fresh (g g^ t1 t2)
       (== g g^)
       (== `(,t1 ,t2) t)
       (== `((,t1)) g)
       (copyo `(,g ,t) `(,g^ ,t^))))
   '((((_.0 _.1) (_.0 _.2)) : (copy (_.1 _.2)))))

  (test
   (run* (t t^)
     (fresh (s )
       (copyo `(,s ,t) `(,s ,t^))
       (== `(,t) s)))
   '((_.0 _.0)))

  (test
   (run* (x y m n g)
     (copyo `(,g (,x ,y)) `((a ,x) (,m ,n)))
     (== `(a ,x) g)) 
   ;;    x   y   m   n    g                y   n
   '(((_.0 _.1 _.0 _.2 (a _.0)) : (copy (_.1 _.2)))))

  (test
   (run* (t t^)
     (fresh (t1 t2)
       (copyo `((,t1) (,t1 ,t2)) `((,t1) ,t^))))
   '((_.0 (_.1 _.2))))

  (test 
   (run* (t t^)
     (fresh (t1 t2)
       (copyo `((,t1) ,t) `((,t1) ,t^))
       (== `(,t1 ,t2) t)))
   '((((_.0 _.1) (_.0 _.2)) : (copy (_.1 _.2)))))

  (test 
   (run* (t t^)
     (fresh (g g^ t1 t2)
       (copyo `(,g ,t) `(,g^ ,t^))
       (== g g^)
       (== `(,t1 ,t2) t)
       (== `((,t1)) g)))
   '((((_.0 _.1) (_.0 _.2)) : (copy (_.1 _.2)))))

  (test
   (run* (x y) 
     (copyo (cons x y) `(1 2))
     (copyo (cons x y) `(1 2 3)))
   '(((_.0 _.1) : (copy (_.0 1) (_.1 (2 . f.2))))))

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4))))
        '((_.0 : (copy (_.0 (f.1 f.2))))))

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '(((_.0 . _.1) : (copy (_.0 f.2) (_.1 (f.3 . f.4))))))

  (test 
   (run* (x y z) (copyo x y) (copyo x z))
   '(((_.0 _.1 _.2) : (copy (_.0 _.1) (_.0 _.2)))))

  (test
   (run* (x y z a1 d1 a2 d2)
     (== `(,a1 . ,d1) y)
     (== `(,a2 . ,d2) z)
     (copyo x y)
     (copyo x z))
   '(((_.0 (_.1 . _.2) (_.3 . _.4) _.1 _.2 _.3 _.4)
      : 
      (copy (_.0 (_.1 . _.2)) (_.0 (_.3 . _.4))))))

  (test (run* (x y) (copyo x y) (== x 5)) '((5 5)))

  (test (run* (x y) (== x 5) (copyo x y)) '((5 5)))

  (test
   (run* (q) (copyo q 5) (copyo q 6))
   '((_.0 : (copy (_.0 f.1)))))

  (test
   (run* (q)
     (fresh (x y)
       (copyo q 5)
       (== `(,x ,y) q)))
   '())
  
  (test (run* (q)
          (fresh (x y)
            (== q `(,x . ,y))
            (copyo q `(1 2))
            (copyo q `(3 4 5 6 7))))
        '(((_.0 . _.1) : (copy (_.0 f.2) (_.1 (f.3 . f.4))))))

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '(((_.0 . _.1) : (copy (_.0 f.2) (_.1 (f.3 . f.4))))))

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4 5 6 7))
            (== q 5)))
        '())

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2))
            (copyo q `(3 4))))
        '((_.0 : (copy (_.0 (f.1 f.2))))))

  (test (run* (x y)
          (copyo x y)
          (copyo y x))
        '((_.0 _.0)))

  (test (run* (x y z)
          (copyo x y)
          (copyo y z)
          (copyo z x)
          (== z x))
        '((_.0 _.0 _.0)))

  (test (run* (q) (fresh (x) (copyo `(,x ,x) q)))
        '((_.0 _.0)))

  (test (run* (q) (fresh (x y) (copyo `((,x) (,x)) y) (== q `(,x ,y))))
        '(((_.0 ((_.1) (_.1))) : (copy (_.0 _.1)))))

  (test (run* (q) (fresh (t x y) (== `((,x) (,x)) t) (copyo t y) (== q `(,t ,y))))
        '(((((_.0) (_.0)) ((_.1) (_.1))) : (copy (_.0 _.1)))))

  (test (run 1 (q) (fresh (x y) (copyo `(lambda (,x) (,y ,x)) q)))
        '((lambda (_.0) (_.1 _.0))))

  (test (run* (q)
          (fresh (x y a b)
            (== x y)
            (copyo `(,x ,y) `(,a ,b))
            (== q `(,x ,y ,a ,b))))
        '(((_.0 _.0 _.1 _.1) : (copy (_.0 _.1)))))

  (test (run* (x y a b)
          (copyo `(,x ,y) `(,a ,b))
          (== x y))
        '(((_.0 _.0 _.1 _.1) : (copy (_.0 _.1)))))

  (test (run* (q)
          (fresh (x g g^ t t^)
            (copyo `(,t ,t) `(,t ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test (run* (x y) (copyo x y))
        '(((_.0 _.1) : (copy (_.0 _.1)))))

  (test (run* (x y z) (=/= y z) (copyo `(,x ,x) `(,y ,z)))
        '())
  
  (test (run* (x y z t) (== `(,x ,x) t) (=/= y z) (copyo t `(,y ,z)))
        '())

  (test (run* (x y z t) (== `(,x ,x) t) (symbol y) (number z) (copyo t `(,y ,z)))
        '())

  (test (run* (x y z t) (== `(,x ,x) t) (absento y z) (copyo t `(,y ,z)))
        '())

  (test (run* (x y z t) (== `(,x (,x)) t) (absento y z) (copyo t `(,y ,z)))
        '())

  (test (run* (x y z t) (== `(,x (,x)) t) (copyo t `(,y ,z)))
        '(((_.0 _.1 (_.1) (_.0 (_.0))) : (copy (_.0 _.1)))))

  (test (run* (x y z t1 t2) (=/= y z) (== `(,x ,x) t1) (copyo t1 t2) (copyo t2 `(,y ,z)))
        '())

  (test (run* (x y z t1 t2 t3) (=/= y z) (== `(,x ,x) t1) (copyo t1 t2) (copyo t2 t3) (copyo t3 `(,y ,z)))
        '())

  (test (run* (q)
          (fresh (x y)
            (== q 5)
            (copyo q `(1 2))
            (copyo q `(3 4))))
        '())

  (test (run* (q)
          (fresh (x y z)
            (== x 5)
            (copyo x y)
            (copyo y z)
            (copyo z x)
            (== q `(,x ,y ,z))))
        '((5 5 5)))

  (test (run* (q)
          (fresh (x y z)
            (== x 5)
            (== y 6)
            (copyo x y)
            (copyo y z)
            (copyo z x)
            (== q `(,x ,y ,z))))
        '())

  (test (run* (a b c d)
          (copyo a b)
          (copyo c d))
        '(((_.0 _.1 _.2 _.3) : (copy (_.0 _.1) (_.2 _.3)))))

  (test (run* (q)
          (fresh (g g^ t t^)
            (== `(,t) g^)
            (copyo `((,t) ,t) `(,g^ ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test (run* (q)
          (fresh (g g^ t t^)
            (== `(,t) g)
            (== g g^)
            (== `(,t ,t^) q)
            (copyo `(,g ,t) `(,g^ ,t^))))
        '((_.0 _.0)))

  (test (run* (q)
          (fresh (g t t^)
            (== `(,t) g)
            (copyo `(,g ,t) `(,g ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test (run* (q)
          (fresh (g g^ t t^ t1 t2)
            (== g g^)
            (== `(-> ,t1 ,t2) t)
            (== `((,t1)) g)
            (== `(,t ,t^) q)
            (copyo `(,g ,t) `(,g^ ,t^))))
        '((((-> _.0 _.1) (-> _.0 _.2)) : (copy (_.1 _.2)))))

  (test (run* (q)
          (fresh (s t t^)
            (== `(,t) s)
            (== `(,t ,t^) q)
            (copyo `(,s ,t) `(,s ,t^))))
        '((_.0 _.0)))

  (test (run* (q)
          (fresh (x g g^ t t^ t1 t2)
            (== g g^)
            (== `(-> ,t1 ,t2) t)
            (== `((x ,t1)) g)
            (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)
            (copyo `(,g ,t) `(,g^ ,t^))))
        '(((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1))) : (copy (_.2 _.3)))))

  (test (run* (q)
          (fresh (x y)
            (copyo q `(1 2 8))
            (copyo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '(((_.0 . _.1) : (copy (_.0 f.2) (_.1 (f.3 f.4 . f.5))))))

  (test (run* (q)
          (copyo q `(1 4))
          (copyo q `(3 4)))
        '((_.0 : (copy (_.0 (f.1 4))))))

  (test (run* (q)
          (copyo q `(3 4))
          (copyo q `(1 4)))
        '((_.0 : (copy (_.0 (f.1 4))))))

  (test (run* (x y z)
          (copyo x `(,y 3 5))
          (copyo x `(,z 4 5)))
        '(((_.0 _.1 _.2) : (copy (_.0 (_.1 3 5)) (_.0 (_.2 4 5))))))

  (test (run* (x y)
          (copyo x `(,y 3 5))
          (copyo x `(,y 4 5)))
        '(((_.0 _.1) : (copy (_.0 (_.1 f.2 5))))))

  (test (run* (x y)
          (copyo x `(,y 4 5))
          (copyo x `(,y 3 5)))
        '(((_.0 _.1) : (copy (_.0 (_.1 f.2 5))))))

  (test (run* (x y z)
          (copyo x `(,y 3 5 ,z))
          (copyo x `(,y 4 5 ,z)))
        '(((_.0 _.1 _.2) : (copy (_.0 (_.1 f.3 5 _.2))))))

  (test (run* (x y z)
          (copyo x `(,y 4 5 ,z))
          (copyo x `(,y 3 5 ,z)))
        '(((_.0 _.1 _.2) : (copy (_.0 (_.1 f.3 5 _.2))))))

  (test (run* (x y z)
          (copyo x `(,y 3 5 ,z))
          (copyo x `(,z 4 5 ,y)))
        '(((_.0 _.1 _.2) : (copy (_.0 (_.1 3 5 _.2)) (_.0 (_.2 4 5 _.1))))))

  (test (run* (x y z)
          (== y 7)
          (copyo x `(,y 3 5 ,z))
          (copyo x `(,z 4 5 ,y)))
        '(((_.0 7 _.1) : (copy (_.0 (7 3 5 _.1)) (_.0 (_.1 4 5 7))))))

  (test (run* (x y z)
          (== y 7)
          (== z 8)
          (copyo x `(,y 3 5 ,z))
          (copyo x `(,z 4 5 ,y)))
        '(((_.0 7 8) : (copy (_.0 (f.1 f.2 5 f.3))))))

  (test (run* (x y z)
          (copyo x `(,y 3 5 ,z))
          (copyo x `(,z 4 5 ,y))
          (== y 7)
          (== z 8))
        '(((_.0 7 8) : (copy (_.0 (f.1 f.2 5 f.3))))))

  (test (run* (x)
          (copyo x `(7 3 5 8))
          (copyo x `(8 4 5 7)))
        '((_.0 : (copy (_.0 (f.1 f.2 5 f.3))))))

  (test (run* (x)
          (copyo x `(3 5))
          (copyo x `(4 5)))
        '((_.0 : (copy (_.0 (f.1 5))))))

  (test (run* (x y)
          (copyo x 3)
          (copyo x y))
        '(((_.0 _.1) : (copy (_.0 3) (_.0 _.1)))))

  (test (run* (x y z)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '(((_.0 _.1 _.2) : (copy (_.0 (_.1 _.2)) (_.0 (_.2 _.1))))))

  (test (run* (x y z)
          (== 5 y)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '(((_.0 5 _.1) : (copy (_.0 (5 _.1)) (_.0 (_.1 5))))))

  (test (run* (x y z)
          (== 5 y)
          (== 5 x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '())

  (test (run* (x a d y z)
          (== 5 y)
          (== `(,a . ,d) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((_.0 . _.1) _.0 _.1 5 _.2)
           : (copy (_.0 5) (_.0 _.2) (_.1 (5)) (_.1 (_.2))))))

  (test (run* (x a d y z)
          (== 5 y)
          (== `(5 . ,d) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((5 . _.0) _.1 _.0 5 5) : (copy (_.0 (5))))))

  (test (run* (x a d y z)
          (== 5 y)
          (== `(5 . ,d) x)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z)))
        '((((5 . _.0) _.1 _.0 5 5) : (copy (_.0 (5))))))

  (test (run* (x a d y z)
          (== 5 y)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z))
          (== `(5 . ,d) x))
        '((((5 . _.0) _.1 _.0 5 5) : (copy (_.0 (5))))))

  (test (run* (x a d y z)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z))
          (== 5 y)
          (== `(5 . ,d) x))
        '((((5 . _.0) _.1 _.0 5 5) : (copy (_.0 (5))))))

  (test (run* (x a b y z)
          (== 5 y)
          (== `(,a ,b) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((_.0 _.1) _.0 _.1 5 _.2)
           : (copy (_.0 5) (_.0 _.2) (_.1 5) (_.1 _.2)))))

  (test (run* (x a b y z)
          (== 5 y)
          (== `(5 ,b) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((5 _.0) _.1 _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x a b y z)
          (== 5 y)
          (== `(,a 5) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((_.0 5) _.0 _.1 5 5) : (copy (_.0 5)))))

  (test (run* (x y z)
          (== 5 y)
          (== 6 z)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '(((_.0 5 6) : (copy (_.0 (f.1 f.2))))))

  (test (run* (x y z)
          (== `(5) x)
          (copyo x `(,y . ,z))
          (copyo x `(,z . ,y)))
        '())

  (test (run* (x a y z)
          (== `(,a 5) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '((((_.0 5) _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x a y z)
          (== `(,a 5) x)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z)))
        '((((_.0 5) _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x a y z)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z))
          (== `(,a 5) x))
        '((((_.0 5) _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x a y z)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y))
          (== `(,a 5) x))
        '((((_.0 5) _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x a y z)
          (copyo x `(,y ,z))
          (== `(,a 5) x)
          (copyo x `(,z ,y)))
        '((((_.0 5) _.0 5 5) : (copy (_.0 5)))))

  (test (run* (x y z)
          (== `(5 5) x)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y)))
        '(((5 5) 5 5)))

  (test (run* (x y z)
          (copyo x `(,y ,z))
          (== `(5 5) x)
          (copyo x `(,z ,y)))
        '(((5 5) 5 5)))

  (test (run* (x y z)
          (copyo x `(,y ,z))
          (copyo x `(,z ,y))
          (== `(5 5) x))
        '(((5 5) 5 5)))

  (test (run* (x y z)
          (copyo x `(,z ,y))
          (copyo x `(,y ,z))
          (== `(5 5) x))
        '(((5 5) 5 5)))

  (test (run* (x a y z)
          (== `(,a 5) x)
          (copyo x `(,y ,z)))
        '((((_.0 5) _.0 _.1 5) : (copy (_.0 _.1)))))

  (test (run* (x a y z)
          (copyo x `(,y ,z))
          (== `(,a 5) x))
        '((((_.0 5) _.0 _.1 5) : (copy (_.0 _.1)))))

  (test (run* (b a y z)
          (== `(,a 5) b)
          (copyo b `(,y ,z)))
        '((((_.0 5) _.0 _.1 5) : (copy (_.0 _.1)))))

  (test (run* (b a y z)
          (copyo b `(,y ,z))
          (== `(,a 5) b))
        '((((_.0 5) _.0 _.1 5) : (copy (_.0 _.1)))))

  (test (run* (b y z)
          (== `(5 6) b)
          (copyo b `(,y ,z)))
        '(((5 6) 5 6)))

  (test (run* (x y)
          (copyo x `(,y))
          (== `(5) x))
        '(((5) 5)))

  (test (run* (b y z)
          (copyo b `(,y ,z))
          (== `(5 6) b))
        '(((5 6) 5 6)))

  (test (run* (a y z)
          (copyo `(,a 5) `(,y ,z))
          (copyo `(,a 5) `(,z ,y)))
        '(((_.0 5 5) : (copy (_.0 5)))))

  (test (run* (a y z)
          (copyo `(,a 5) `(,z ,y))
          (copyo `(,a 5) `(,y ,z)))
        '(((_.0 5 5) : (copy (_.0 5)))))

  (test (run* (a y z)
          (copyo a y)
          (copyo a z)
          (copyo 5 a))
        '((5 5 5)))

  (test (run* (a y z)
          (copyo a y)
          (copyo 5 a)
          (copyo a z))
        '((5 5 5)))

  (test (run* (a y z)
          (copyo 5 a)
          (copyo a y)
          (copyo a z))
        '((5 5 5)))

  (test (run* (a y z)
          (copyo a y)
          (copyo a z)
          (== 5 a))
        '((5 5 5)))

  (test (run* (a y z)
          (copyo a z)
          (copyo a y)
          (== 5 a))
        '((5 5 5)))

  (test (run* (a y z)
          (== 5 a)
          (copyo a z)
          (copyo a y))
        '((5 5 5)))

  (test (run* (a x y z)
          (copyo `(,a 5) `(,x ,y))
          (copyo `(,a 5) `(,y ,z))
          (copyo `(,a 5) `(,z ,x)))
        '(((_.0 5 5 5) : (copy (_.0 5)))))

  (test (run* (a x y z)
          (copyo `(,a 5) `(,x ,y))
          (copyo `(,a 5) `(,z ,x))
          (copyo `(,a 5) `(,y ,z)))
        '(((_.0 5 5 5) : (copy (_.0 5)))))

  (test (run* (x a b c d e f)
          (copyo `(,x 5) `(,a ,b))
          (copyo `(,x 5) `(,b ,c))
          (copyo `(,x 5) `(,c ,d))
          (copyo `(,x 5) `(,d ,e))
          (copyo `(,x 5) `(,e ,f))
          (copyo `(,x 5) `(,f ,a)))
        '(((_.0 5 5 5 5 5 5) : (copy (_.0 5)))))

  (test (run* (x a b c d e f)
          (copyo `(,x 5) `(,a ,b))
          (copyo `(,x 5) `(,b ,c))
          (copyo `(,x 5) `(,c ,d))
          (copyo `(,x 5) `(,d ,e))
          (copyo `(,x 5) `(,e ,f)))
        '(((_.0 _.1 5 5 5 5 5) : (copy (_.0 5) (_.0 _.1)))))

  (test (run* (x a b c d e f)
          (copyo `(,x 5) `(,e ,f))
          (copyo `(,x 5) `(,d ,e))
          (copyo `(,x 5) `(,a ,b))
          (copyo `(,x 5) `(,b ,c))
          (copyo `(,x 5) `(,c ,d)))
        '(((_.0 _.1 5 5 5 5 5) : (copy (_.0 5) (_.0 _.1)))))

  )

