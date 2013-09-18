#lang racket

(require
 "../tester.rkt"
 "../ck.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../matche.rkt"
 "../src/operators.rkt")

(provide distincto rembero test-neq test-neq-long)

(defmatche (distincto l)
  [[()]]
  [[(,a)]]
  [[(,a ,ad . ,dd)]
   (=/= a ad)
   (distincto `(,a . ,dd))
   (distincto `(,ad . ,dd))])

(defmatche (rembero x ls out)
  [[,x () ()]]
  [[,x (,x . ,d) ,out]
   (rembero x d out)]
  [[,x (,a . ,d) ,out]
   (=/= a x)
   (fresh (res)
     (rembero x d res)
     (== `(,a . ,res) out))])

(define (test-neq)

  ;; SIMPLE

  (test (run* (q) (=/= 5 6)) '(_.0))
  
  (test (run* (q) (=/= 3 3)) '())
  
  (test (run* (q) (== q 3) (=/= 3 q))
        '())
  
  (test (run* (q) (=/= 3 q) (== q 3))
        '())
  
  (test (run* (x y) (== x y) (=/= x y))
        '())
  
  (test (run* (x y) (=/= x y) (== x y))
        '())

  (test (run* (q) (=/= q q))
        '())

  (test (run* (q) (fresh (a) (=/= a a)))
        '())
  
  (test
   (run* (x y)
     (=/= x y)
     (== 3 x)
     (== 3 y))
   '())
  
  (test
   (run* (x y)
     (== 3 x)
     (=/= x y)
     (== 3 y))
   '())
  
  (test
   (run* (x y)
     (== 3 x)
     (== 3 y)
     (=/= x y))
   '())
  
  (test
   (run* (x y)
     (== 3 x)
     (== 3 y)
     (=/= y x))
   '())
  
  (test
   (run* (x y z)
     (== x y)
     (== y z)
     (=/= x 4)
     (== z (+ 2 2)))
   '())
  
  (test
   (run* (x y z)
     (== x y)
     (== y z)
     (== z (+ 2 2))
     (=/= x 4))
   '())
  
  (test
   (run* (x y z)
     (=/= x 4)
     (== y z)
     (== x y)
     (== z (+ 2 2)))
   '())
  
  (test
   (run* (x y z)
     (=/= x y)
     (== x `(0 ,z 1))
     (== y `(0 1 1))
     (== z 1))
   '())
  
  (test
   (run* (x y z)
     (== z 1)
     (=/= x y)
     (== x `(0 ,z 1))
     (== y `(0 1 1)))
   '())
  
  (test
   (run* (x y z)
     (== z 1)
     (== x `(0 ,z 1))
     (== y `(0 1 1))
     (=/= x y))
   '())
  
  (test
   (run* (q)
     (fresh (x y z)
       (=/= x y)
       (== x `(0 ,z 1))
       (== y `(0 1 1))
       (== z 0)))
   '(_.0))
  
  (test
   (run* (x y)
     (=/= `(,x 1) `(2 ,y))
     (== x 2)
     (== y 1))
   '())

  (test
   (run* (a x z)
     (=/= a `(,x 1))
     (== a `(,z 1))
     (== x z))
   '())

  (test
   (run* (x y)
     (=/= `(,x 1) `(2 ,y))
     (== x 2)
     (== y 1))
   '())
  
  (test
   (run* (q)
     (fresh (x y z)
       (== z 0)
       (=/= x y)
       (== x `(0 ,z 1))
       (== y `(0 1 1))))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (x y z)
       (== x `(0 ,z 1))
       (== y `(0 1 1))
       (=/= x y)))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (x y)
       (=/= `(,x 1) `(2 ,y))
       (== x 2)))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (x y)
       (=/= `(,x 1) `(2 ,y))
       (== y 1)))
   '(_.0))
  
  (test
   (run* (x y z)
     (=/= `(,x 2 ,z) `(1 ,z 3))
     (=/= `(,x 6 ,z) `(4 ,z 6))
     (=/= `(,x ,y ,z) `(7 ,z 9))
     (== x z))
   '((_.0 _.1 _.0)))
  
  (test
   (run* (x y)
     (=/= `(,x 1) `(2 ,y))
     (== x 2)
     (== y 9))
   '((2 9)))
  
  (test
   (run* (q)
     (fresh (a)
       (== 3 a)
       (=/= a 4)))
   '(_.0))

  ;; MEDIUM

  ;; these test reification
  (test
   (run* (q) (=/= q #f))
   '((_.0 : (=/= ((_.0 . #f))))))
  
  (test
   (run* (x y) (=/= x y))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))))))
  
  ;; this tests the constraint-interaction
  (test
   (run* (q) 
     (=/= q 5)
     (=/= 5 q))
   '((_.0 : (=/= ((_.0 . 5))))))

  (test
   (run* (x y)
     (=/= y x))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (x y)
     (=/= x y)
     (=/= x y))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))))))
  
  (test
   (run* (x y)
     (=/= x y)
     (=/= y x))
   '(((_.0 _.1) : (=/= ((_.0 . _.1)))))) 
  
  (test
   (run* (x y)
     (=/= `(,x 1) `(2 ,y)))
   '(((_.0 _.1) : (=/= ((_.0 . 2) (_.1 . 1))))))
  
  (test
   (run* (q)
     (=/= 4 q)
     (=/= 3 q))
   '((_.0 : (=/= ((_.0 . 3)) ((_.0 . 4))))))

  (test
   (run* (q) (=/= q 5) (=/= q 5))
   '((_.0 : (=/= ((_.0 . 5))))))

  ;; HARD
  
  (test
   (run* (x y)
     (=/= `(,x 1) `(2 ,y))
     (== x 2))
   '(((2 _.0) : (=/= ((_.0 . 1))))))
  
  (test
   (run* (q)
     (fresh (a x z)
       (=/= a `(,x 1))
       (== a `(,z 1))
       (== x 5)
       (== `(,x ,z) q)))
   '(((5 _.0) : (=/= ((_.0 . 5))))))
  
  (test
   (run* (x y)
     (=/= `(,x ,y) `(5 6))
     (=/= x 5))
   '(((_.0 _.1) : (=/= ((_.0 . 5))))))
  
  (test
   (run* (x y)
     (=/= x 5)
     (=/= `(,x ,y) `(5 6)))
   '(((_.0 _.1) : (=/= ((_.0 . 5))))))
  
  (test
   (run* (x y)
     (=/= 5 x)
     (=/= `( ,y ,x) `(6 5)))
   '(((_.0 _.1) : (=/= ((_.0 . 5))))))
  
  (test
   (run* (x)
     (fresh (y z)
       (=/= x `(,y 2))
       (== x `(,z 2))))
   '((_.0 2)))
  
  (test
   (run* (x)
     (fresh (y z)
       (=/= x `(,y 2))
       (== x `((,z) 2))))
   '(((_.0) 2)))
  
  (test
   (run* (x)
     (fresh (y z)
       (=/= x `((,y) 2))
       (== x `(,z 2))))
   '((_.0 2)))
  
  (test
   (run* (q)
     (distincto `(2 3 ,q)))
   '((_.0 : (=/= ((_.0 . 2)) ((_.0 . 3))))))
  
  (test
   (run* (q) (rembero 'x '() q))
   '(()))

  (test
   (run* (q) (rembero 'x '(x) '()))
   '(_.0))
  
  (test
   (run* (q) (rembero 'a '(a b a c) q))
   '((b c)))
  
  (test
   (run* (q) (rembero 'a '(a b c) '(a b c)))
   '())

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z)))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3))))))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (== w y))
   '(((_.0 _.1 _.0 _.2)
      :
      (=/= ((_.1 . _.2))))))
  )

(define (test-neq-long)
  (test-neq))

(module+ main
  (test-neq-long))

