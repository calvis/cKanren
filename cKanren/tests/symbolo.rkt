#lang racket

(require
 "../ck.rkt"
 "../tree-unify.rkt"
 "../attributes.rkt"
 "../neq.rkt"
 "../tester.rkt"
 "../src/operators.rkt")

(provide test-symbol test-symbol-long)

(define (test-symbol)

  (test
   (run* (q) (symbol q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (symbol q) (symbol q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (x y) (symbol x) (symbol y))
   '(((_.0 _.1) : (symbol _.0 _.1))))

  (test
   (run* (q) (symbol q) (== 'x q))
   '(x))

  (test
   (run* (q) (== 'x q) (symbol q))
   '(x))

  (test
   (run* (q) (== 5 q) (symbol q))
   '())

  (test
   (run* (q) (symbol q) (== 5 q))
   '())

  (test
   (run* (q) (== `(1 . 2) q) (symbol q))
   '())

  (test
   (run* (q) (symbol q) (== `(1 . 2) q))
   '())

  (test
   (run* (q) (fresh (x) (symbol x)))
   '(_.0))
  
  (test
   (run* (q) (fresh (x) (== x q) (symbol x)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (symbol x) (== x q)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (== x q) (symbol q) (symbol x)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (symbol q) (== x q) (symbol x)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (symbol q) (symbol x) (== x q)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (symbol q) (== 'y x)))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (fresh (x) (symbol q) (== 'y x) (== x q)))
   '(y))

  (test
   (run* (q) (fresh (x) (== q x) (symbol q) (== 5 x)))
   '())

  (test
   (run* (q) (symbol q) (=/= 5 q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (=/= 5 q) (symbol q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (symbol q) (=/= `(1 . 2) q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (symbol q) (=/= 'y q))
   '((_.0 : (=/= ((_.0 . y))) (symbol _.0))))

  (test
   (run* (x y)
     (symbol x)
     (symbol y))
   '(((_.0 _.1) : (symbol _.0 _.1))))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (symbol z))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3)))
      (symbol _.3))))

  (test
   (run* (q)
     (fresh (w x y z)
       (=/= `(,w . ,x) `(,y . ,z))
       (symbol w)
       (symbol z)))
   '(_.0))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (symbol w)
     (symbol z))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3)))
      (symbol _.0 _.3))))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (symbol w)
     (symbol y))
   '(((_.0 _.1 _.2 _.3)
      :
      (=/= ((_.0 . _.2) (_.1 . _.3)))
      (symbol _.0 _.2))))

  (test
   (run* (w x y z)
     (=/= `(,w . ,x) `(,y . ,z))
     (symbol w)
     (symbol y)
     (== w y))
   '(((_.0 _.1 _.0 _.2)
      :
      (=/= ((_.1 . _.2)))
      (symbol _.0))))

  (test
   (run* (w x)
     (=/= `(,w . ,x) `(5 . 6))
     (symbol w))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (w x)
     (symbol w)
     (=/= `(,w . ,x) `(5 . 6)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (w x)
     (symbol w)
     (=/= `(5 . 6) `(,w . ,x)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (w x)
     (symbol w)
     (=/= `(5 . ,x) `(,w . 6)))
   '(((_.0 _.1) : (symbol _.0))))

  (test
   (run* (w x)
     (symbol w)
     (=/= `(z . ,x) `(,w . 6)))
   '(((_.0 _.1) : (=/= ((_.0 . z) (_.1 . 6))) (symbol _.0))))

  (test
   (run* (w x y z)
     (== x 5)
     (=/= `(,w ,y) `(,x ,z))
     (== w 5))
   '(((5 5 _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (=/= `(,w ,y) `(,x ,z))
     (== w 5)
     (== x 5))
   '(((5 5 _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (== w 5)
     (=/= `(,w ,y) `(,x ,z))
     (== x 5))
   '(((5 5 _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (== w 5)
     (== x 5)
     (=/= `(,w ,y) `(,x ,z)))
   '(((5 5 _.0 _.1) : (=/= ((_.0 . _.1))))))


  (test
   (run* (w x y z)
     (== x 'a)
     (=/= `(,w ,y) `(,x ,z))
     (== w 'a))
   '(((a a _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (=/= `(,w ,y) `(,x ,z))
     (== w 'a)
     (== x 'a))
   '(((a a _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (== w 'a)
     (=/= `(,w ,y) `(,x ,z))
     (== x 'a))
   '(((a a _.0 _.1) : (=/= ((_.0 . _.1))))))

  (test
   (run* (w x y z)
     (== w 'a)
     (== x 'a)
     (=/= `(,w ,y) `(,x ,z)))
   '(((a a _.0 _.1) : (=/= ((_.0 . _.1))))))
  )

(define (test-symbol-long)
  (test-symbol))

(module+ main
  (test-symbol-long))

