#lang racket

(require "ck.rkt" 
         "tree-unify.rkt"
         "src/framework.rkt"
         "src/operators.rkt")

(provide templateo)

;; goal that will copy the "template" in t, i.e. the structure and
;; free variables, to x
(define (templateo t x)
  (fresh (gensym)
    (template t x gensym)))

;; if t is an mk-struct, copies that structure onto x.  if t is ground
;; or if there is already a (template x t) constraint, this constraint
;; turns into ==. otherwise, placed back in the store.
(define-constraint (template [t walk*] x [sym #:constant])
  (transformer
   #:package (a [s c e])
   (cond
    [(and (eq? t x) (var? t))
     (add-constraint (template t x sym))]
    [(eq? t x) succeed]
    [(occurs-check x t s) fail]
    [(pair? t)
     (fresh (first rest)
       (== x `(,first . ,rest))
       (template (car t) first sym)
       (template (cdr t) rest sym))]
    [(not (var? t)) (== t x)]
    [else (add-constraint (template t x sym))])))

(define-constraint-interaction
  template-same-args
  [(template ,t ,x ,sym1) (template ,x ,t ,sym2)] 
  [(not (eq? t x))
   [(== t x) (template x x sym1) (template x x sym2)]])

(define-constraint-interaction
  template-unify
  [(template ,x ,y ,sym) (template ,x ,z ,sym)] 
  => 
  [(template x y sym) (== y z)])

(module+ test
  (require "tester.rkt")

  (test (run* (q) (templateo 5 5)) '(_.0))

  (test (run* (q) (templateo q q)) '(_.0))
  (test (run* (q) (templateo 5 q)) '(5))
  (test (run* (q) (templateo q 5) (templateo q 6)) '(_.0))
  (test (run* (q) 
          (fresh (x y)
            (templateo q 5)
            (== `(,x ,y) q)))
        '())

  (test (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '((_.0 . _.1)))

  (test (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q 5)))
        '())
  (test (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4))))
        '(_.0))

  #;
  (test "8"
        (run* (q)
          (fresh (x y z)
            (templateo x y)
            (templateo y z)
            (templateo z x)
            (== q `(,x ,y ,z))))
        '((_.0 _.0 _.0)))


  (test (run* (q) (templateo `(,q) q)) '())

  (test (run* (q)
          (fresh (x) 
            (templateo `(,x ,x) q)))
        '((_.0 _.0)))

  (test (run* (q) (fresh (x y) (templateo `((,x) (,x)) y) (== q `(,x ,y))))
        '((_.0 ((_.1) (_.1)))))

  (test (run 1 (q) (fresh (x y) (templateo `(lambda (,x) (,y ,x)) q)))
        '((lambda (_.0) (_.1 _.0))))

  (test (run* (q)
          (fresh (x y a b)
            (== x y)
            (templateo `(,x ,y) `(,a ,b))
            (== q `(,x ,y ,a ,b))))
        '((_.0 _.0 _.1 _.1)))

  (test (run* (q)
          (fresh (x y a b)
            (templateo `(,x ,y) `(,a ,b))
            (== x y)
            (== q `(,x ,y ,a ,b))))
        '((_.0 _.0 _.1 _.1)))

  (test 
    (run* (q)
      (fresh (x g g^ t t^)
        (templateo `(,t ,t) `(,t ,t^))
        (== `(,t ,t^) q)))
    '((_.0 _.0)))
  
  (test 
        (run* (q)
          (fresh (g g^ t t^)
            (== `(,t) g^)
            (templateo `((,t) ,t) `(,g^ ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test 
        (run* (q)
          (fresh (g g^ t t^)
            (templateo `(,g ,t) `(,g^ ,t^))
            (== `(,t) g)
            (== g g^)
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test 
        (run* (q)
          (fresh (g t t^)
            (== `(,t) g)
            (templateo `(,g ,t) `(,g ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test 
        (run* (q)
          (fresh (g g^ t t^ t1 t2)
            (== g g^)
            (== `(-> ,t1 ,t2) t)
            (== `((,t1)) g)
            (== `(,t ,t^) q)
            (templateo `(,g ,t) `(,g^ ,t^))))
        '(((-> _.0 _.1) (-> _.0 _.2))))

  (test
    (run* (q)
      (fresh (s t t^)
        (templateo `(,s ,t) `(,s ,t^))
        (== `(,t) s)
        (== `(,t ,t^) q)))
    '((_.0 _.0)))

  (test
    (run* (x y m n g)
      (templateo `(,g (,x ,y)) `((a ,x) (,m ,n)))
      (== `(a ,x) g)) ;; first thing in z should be x
    ;; x   y    x   ?       x
    '((_.0 _.1 _.0 _.2 (a _.0))))

  (test 
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1))))) 

)

