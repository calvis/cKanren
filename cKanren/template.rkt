#lang racket

(require "ck.rkt" "tree-unify.rkt")

(provide templateo)

;; goal that will copy the "template" in t, i.e. the structure and
;; free variables, to x
(define (templateo t x)
  (fresh (gensym)
    (template t x gensym)))

;; if t is an mk-struct, copies that structure onto x.  if t is ground
;; or if there is already a (template x t) constraint, this constraint
;; turns into ==. otherwise, placed back in the store.
(define-constraint 
  (template [t walk*] x [sym #:constant])
  #:package (a : s c)
  (cond
   [(eq? t x) 
    (update-c (build-oc template t x sym))]
   [(occurs-check x t s) fail]
   [(pair? t)
    (fresh (first rest)
      (conj
       (== x `(,first . ,rest))
       (template (car t) first sym)
       (template (cdr t) rest sym)))]
   [(not (var? t)) (== t x)]
   [else (update-c (build-oc template t x sym))]))

(define-constraint-interaction
  [(template ,t ,x ,sym1) (template ,x ,t ,sym2)] 
  => 
  [(== t x) (template x x sym1) (template x x sym2)])

(define-constraint-interaction
  [(template ,x ,y ,sym) (template ,x ,z ,sym)] 
  => 
  [(template x y sym) (== y z)])

(module+ test
  (require "tester.rkt")

  ;; sanity
  (test (run* (q) succeed) '(_.0))
  (test (run* (q) fail) '())

  (test (run* (q) (== 5 5)) '(_.0))
  (test "0" (run* (q) (templateo 5 5)) '(_.0))

  (test "1" (run* (q) (templateo q q)) '(_.0))
  (test "2" (run* (q) (templateo 5 q)) '(5))
  (test "3" (run* (q) (templateo q 5) (templateo q 6)) '(_.0))
  (test "4" 
        (run* (q) 
          (fresh (x y)
            (templateo q 5)
            (== `(,x ,y) q)))
        '())

  (test "5"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '((_.0 . _.1)))

  (test "6"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q 5)))
        '())
  (test "7"
        (run* (q)
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


  (test "9" (run* (q) (templateo `(,q) q)) '())

  (test "10"
        (run* (q)
          (fresh (x) 
            (templateo `(,x ,x) q)))
        '((_.0 _.0)))

  (test "11"
        (run* (q) (fresh (x y) (templateo `((,x) (,x)) y) (== q `(,x ,y))))
        '((_.0 ((_.1) (_.1)))))

  (test "12"
        (run 1 (q) (fresh (x y) (templateo `(lambda (,x) (,y ,x)) q)))
        '((lambda (_.0) (_.1 _.0))))

  (test "13"
        (run* (q)
          (fresh (x y a b)
            (== x y)
            (templateo `(,x ,y) `(,a ,b))
            (== q `(,x ,y ,a ,b))))
        '((_.0 _.0 _.1 _.1)))

  (test "14"
        (run* (q)
          (fresh (x y a b)
            (templateo `(,x ,y) `(,a ,b))
            (== x y)
            (== q `(,x ,y ,a ,b))))
        '((_.0 _.0 _.1 _.1)))

  (test "15"
    (run* (q)
      (fresh (x g g^ t t^)
        (templateo `(,t ,t) `(,t ,t^))
        (== `(,t ,t^) q)))
    '((_.0 _.0)))
  
  (test "16.1"
        (run* (q)
          (fresh (g g^ t t^)
            (== `(,t) g^)
            (templateo `((,t) ,t) `(,g^ ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test "16.2"
        (run* (q)
          (fresh (g g^ t t^)
            (templateo `(,g ,t) `(,g^ ,t^))
            (== `(,t) g)
            (== g g^)
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test "16.3"
        (run* (q)
          (fresh (g t t^)
            (== `(,t) g)
            (templateo `(,g ,t) `(,g ,t^))
            (== `(,t ,t^) q)))
        '((_.0 _.0)))

  (test "16.4"
        (run* (q)
          (fresh (g g^ t t^ t1 t2)
            (== g g^)
            (== `(-> ,t1 ,t2) t)
            (== `((,t1)) g)
            (== `(,t ,t^) q)
            (templateo `(,g ,t) `(,g^ ,t^))))
        '(((-> _.0 _.1) (-> _.0 _.2))))

  (test "16.5"
    (run* (q)
      (fresh (s t t^)
        (templateo `(,s ,t) `(,s ,t^))
        (== `(,t) s)
        (== `(,t ,t^) q)))
    '((_.0 _.0)))

  (test "16.6"
    (run* (q)
      (fresh (x g g^ t t^ t1 t2)
        (templateo `(,g ,t) `(,g^ ,t^))
        (== g g^)
        (== `(-> ,t1 ,t2) t)
        (== `((x ,t1)) g)
        (== `(,x ,t ,t1 ,t2 ,t^ ,g ,g^) q)))
    '((_.0 (-> _.1 _.2) _.1 _.2 (-> _.1 _.3) ((x _.1)) ((x _.1))))) 

)

