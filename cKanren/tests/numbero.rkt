#lang racket

(require
 "../ck.rkt"
 "../attributes.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../tester.rkt")

(provide test-number test-number-long)

(define (test-number)
  (test
   (run* (q) (number q))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (number q) (== 5 q))
   '(5))
  
  (test
   (run* (q) (== 5 q) (number q))
   '(5))

  (test
   (run* (q) (== 'x q) (number q))
   '())
  
  (test
   (run* (q) (number q) (== 'x q))
   '())
  
  (test
   (run* (q) (number q) (== `(1 . 2) q))
   '())
  
  (test
   (run* (q) (== `(1 . 2) q) (number q))
   '())
  
  (test
   (run* (q) (fresh (x) (number x)))
   '(_.0))
  
  (test
   (run* (q) (fresh (x) (number x)))
   '(_.0))
  
  (test
   (run* (q) (fresh (x) (number x) (== x q)))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (fresh (x) (number q) (== x q) (number x)))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (fresh (x) (number q) (number x) (== x q)))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (fresh (x) (== x q) (number q) (number x)))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (fresh (x) (number q) (== 5 x)))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (fresh (x) (number q) (== 5 x) (== x q)))
   '(5))
  
  (test
   (run* (q) (fresh (x) (== q x) (number q) (== 'y x)))
   '())
  
  (test
   (run* (q) (number q) (=/= 'y q))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (=/= 'y q) (number q))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (number q) (=/= `(1 . 2) q))
   '((_.0 : (number _.0))))
  
  (test
   (run* (q) (number q) (=/= 5 q))
   '((_.0 : (=/= ((_.0 . 5))) (number _.0))))
  
  (test
   (run* (x y)
     (number x)
     (number y))
   '(((_.0 _.1) : (number _.0 _.1))))
  
  (test
   (run* (x y)
     (number x)
     (number x))
   '(((_.0 _.1) : (number _.0))))
  
  (test
   (run* (q)
     (fresh (w x y z)
       (=/= `(,w . ,x) `(,y . ,z))
       (number w)
       (number z)))
   '(_.0))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (number w)
     (number z))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3)))
      (number _.0 _.3))))
  
  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (number w)
     (number y))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3)))
      (number _.0 _.2))))
  
  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (number w)
     (number y)
     (== w y))
   '(((_.0 _.1 _.0 _.2)
      :
      (=/= ((_.1 . _.2)))
      (number _.0))))
  
  (test
   (run* (w x) (=/= `(,w . ,x) `(a . b)))
   '(((_.0 _.1) : (=/= ((_.0 . a) (_.1 . b))))))

  (test
   (run* (w x)
     (=/= `(,w . ,x) `(a . b))
     (number w))
   '(((_.0 _.1) : (number _.0))))

  (test
   (run* (w x)
     (number w)
     (=/= `(,w . ,x) `(a . b)))
   '(((_.0 _.1) : (number _.0))))

  (test
   (run* (w x)
     (number w)
     (=/= `(a . b) `(,w . ,x)))
   '(((_.0 _.1) : (number _.0))))

  (test
   (run* (w x)
     (number w)
     (=/= `(a . ,x) `(,w . b)))
   '(((_.0 _.1) : (number _.0))))

  (test
   (run* (w x)
     (number w)
     (=/= `(5 . ,x) `(,w . b)))
   '(((_.0 _.1) : (=/= ((_.0 . 5) (_.1 . b))) (number _.0))))
  
  (test
   (run* (x y z a b)
     (number x)
     (number y)
     (number z)
     (number a)
     (number b)
     (== `(,y ,z ,x ,b) `(,z ,x ,y ,a)))
   '(((_.0 _.0 _.0 _.1 _.1) : (number _.0 _.1))))
  
  (test
   (run* (x y z a b)
     (== `(,y ,z ,x ,b) `(,z ,x ,y ,a))
     (number x)
     (number a))
   '(((_.0 _.0 _.0 _.1 _.1) : (number _.0 _.1))))
  )

(define (test-number-long)
  (test-number))

(module+ main
  (test-number-long))
