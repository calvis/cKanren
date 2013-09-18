#lang racket

(require
 "../ck.rkt"
 "../tree-unify.rkt"
 "../attributes.rkt"
 "../neq.rkt"
 "../tester.rkt")

(provide test-symbol-number
         test-symbol-number-long)

(define (test-symbol-number)
  (test
   (run* (q) (symbol q) (number q))
   '())

  (test
   (run* (q) (number q) (symbol q))
   '())

  (test
   (run* (q)
     (fresh (x)
       (number x)
       (symbol x)))
   '())

  (test
   (run* (q)
     (fresh (x)
       (symbol x)
       (number x)))
   '())

  (test
   (run* (q)
     (number q)
     (fresh (x)
       (symbol x)
       (== x q)))
   '())

  (test
   (run* (q)
     (symbol q)
     (fresh (x)
       (number x)
       (== x q)))
   '())

  (test
   (run* (q)
     (fresh (x)
       (number x)
       (== x q))
     (symbol q))
   '())

  (test
   (run* (q)
     (fresh (x)
       (symbol x)
       (== x q))
     (number q))
   '())

  (test
   (run* (q)
     (fresh (x)
       (== x q)
       (symbol x))
     (number q))
   '())

  (test
   (run* (q)
     (fresh (x)
       (== x q)
       (number x))
     (symbol q))
   '())

  (test
   (run* (q)
     (symbol q)
     (fresh (x)
       (number x)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q)
     (number q)
     (fresh (x)
       (symbol x)))
   '((_.0 : (number _.0))))

  (test
   (run* (q)    
     (fresh (x y)
       (symbol x)
       (== `(,x ,y) q)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)    
     (fresh (x y)
       (number x)
       (== `(,x ,y) q)))
   '(((_.0 _.1) : (number _.0))))

  (test
   (run* (q)    
     (fresh (x y)
       (number x)
       (symbol y)
       (== `(,x ,y) q)))
   '(((_.0 _.1) : (number _.0) (symbol _.1))))

  (test
   (run* (q)    
     (fresh (x y)
       (number x)
       (== `(,x ,y) q)
       (symbol y)))
   '(((_.0 _.1) : (number _.0) (symbol _.1))))

  (test
   (run* (q)    
     (fresh (x y)
       (== `(,x ,y) q)
       (number x)
       (symbol y)))
   '(((_.0 _.1) : (number _.0) (symbol _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (number x)
       (symbol y))
     (fresh (w z)
       (== `(,w ,z) q)))
   '(((_.0 _.1) : (number _.0) (symbol _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (number x)
       (symbol y))
     (fresh (w z)
       (== `(,w ,z) q)
       (== w 5)))
   '(((5 _.0) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (number x)
       (symbol y))
     (fresh (w z)
       (== 'a z)
       (== `(,w ,z) q)))
   '(((_.0 a) : (number _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (number x)
       (symbol y))
     (fresh (w z)
       (== `(,w ,z) q)
       (== 'a z)))
   '(((_.0 a) : (number _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (=/= `(5 a) q)))
   '(((_.0 _.1) : (=/= ((_.0 . 5) (_.1 . a))))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (=/= `(5 a) q)
       (symbol x)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (symbol x)
       (=/= `(5 a) q)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (symbol x)
       (== `(,x ,y) q)
       (=/= `(5 a) q)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (=/= `(5 a) q)
       (symbol x)
       (== `(,x ,y) q)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (=/= `(5 a) q)
       (== `(,x ,y) q)
       (symbol x)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (=/= `(5 a) q)
       (number y)))
   '(((_.0 _.1) : (number _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (== `(,x ,y) q)
       (number y)
       (=/= `(5 a) q)))
   '(((_.0 _.1) : (number _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (number y)
       (== `(,x ,y) q)
       (=/= `(5 a) q)))
   '(((_.0 _.1) : (number _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (=/= `(5 a) q)
       (number y)
       (== `(,x ,y) q)))
   '(((_.0 _.1) : (number _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (=/= `(5 a) q)
       (== `(,x ,y) q)
       (number y)))
   '(((_.0 _.1) : (number _.1))))

  (test
   (run* (q)
     (fresh (x y)
       (=/= `(,x ,y) q)
       (number x)
       (symbol y)))
   '(_.0))

  (test
   (run* (q)
     (fresh (x y)
       (number x)
       (=/= `(,x ,y) q)
       (symbol y)))
   '(_.0))

  (test
   (run* (q)
     (fresh (x y)
       (number x)
       (symbol y)
       (=/= `(,x ,y) q)))
   '(_.0))
  )

(define (test-symbol-number-long)
  (test-symbol-number))

(module+ main
  (test-symbol-number-long))

