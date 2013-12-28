#lang racket

(require 
 "../ck.rkt"
 "../absento.rkt"
 "../attributes.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../tester.rkt")
(provide test-absento test-absento-long)

(define (test-absento)
  (test
   (run* (q) (absento q q))
   '())

  (test 
   (run* (q) (absento q 5))
   '((_.0 : (=/= ((_.0 . 5))))))

  (test
   (run* (x y) (absento x y))
   '(((_.0 _.1) : (absento (_.0 _.1)))))

  (test
   (run* (x y) (absento x y) (== x y))
   '())
  
  (test
   (run* (q)
     (fresh (a b c)
       (== a b)
       (absento b c)
       (== c b)
       (== `(,a ,b ,c) q)))
   '())

  (test
   (run* (q)
     (fresh (a)
       (absento q a)
       (absento `((,q ,q) 3 (,q ,q)) `(,a 3 ,a))))
   '(_.0))

  (test
   (run* (a b)
     (absento `(3 ,a) `(,b ,a))
     (== 3 b))
   '())

  (test
   (run* (q)
     (fresh (a b)
       (absento q a)
       (absento `(3 ,a) `(,q ,a))
       (== 3 b)))
   '((_.0 : (=/= ((_.0 . 3))))))
  
  (test
   (run* (q)
     (number q)
     (absento '(3) q))
   '((_.0 : (number _.0))))

  (test
   (run* (q)
     (symbol q)
     (absento '(3) q))
   '((_.0 : (symbol _.0))))
  
  (test
   (run* (a b)
     (number a)
     (number b)
     (absento '(3 3) `(,a ,b))
     (=/= a b))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))) (number _.0 _.1))))

  (test
   (run* (q) (fresh (a) (absento q a) (== q a)))
   '())

  (test
   (run* (q)
     (fresh (a b c)
       (absento '(3 . 4) c)
       (== `(,a . ,b) c)
       (== q `(,a . ,b))))
   '(((_.0 . _.1)
      :
      (=/= ((_.0 . 3) (_.1 . 4)))
      (absento ((3 . 4) _.0) ((3 . 4) _.1)))))
  
  (test
   (run* (q)
     (fresh (a b)
       (absento 5 a)
       (symbol b)
       (== `(,q ,b) a)))
   '((_.0 : (absento (5 _.0)))))

  (test
   (run* (q)
     (fresh (a b)
       (absento 5 a)
       (== `(,q ,b) a)))
   '((_.0 : (absento (5 _.0)))))

  (test
   (run* (q) 
     (fresh (a) 
       (absento `(3 . ,a) q)
       (absento q `(3 . ,a))))
   '((_.0 : (=/= ((_.0 . 3))))))
  
  (test
   (run* (q)
     (fresh (a b c d e f)
       (absento `(,a . ,b) q)
       (absento q `(,a . ,b))
       (== `(,c . ,d) a)
       (== `(3 . ,e) c)
       (== `(,f . 4) d)))
   '((_.0 : (=/= ((_.0 . 3)) ((_.0 . 4))))))

  (test
   (run* (a b c)
     (number b)
     (absento `(,3 . ,a) `(,b . ,c)))
   '(((_.0 _.1 _.2) 
      :
      (=/= ((_.0 . _.2) (_.1 . 3)))
      (absento ((3 . _.0) _.2))
      (number _.1))))

  (test
   (run* (a b c)
     (absento `(,3 . ,a) `(,b . ,c))
     (number b))
   '(((_.0 _.1 _.2) 
      :
      (=/= ((_.0 . _.2) (_.1 . 3)))
      (absento ((3 . _.0) _.2))
      (number _.1))))

  (test
   (run* (q)
     (fresh (a b c)
       (== `(,a . ,b) q)
       (absento '(3 . 4) q)
       (number a)
       (number b)))
   '(((_.0 . _.1) : (=/= ((_.0 . 3) (_.1 . 4))) (number _.0 _.1))))

  (test
   (run* (q)
     (fresh (a b)
       (absento '(3 . 4) `(,a . ,b))
       (== `(,a . ,b) q)))
   '(((_.0 . _.1) 
      :
      (=/= ((_.0 . 3) (_.1 . 4)))
      (absento ((3 . 4) _.0) ((3 . 4) _.1)))))

  (test
   (run* (q)
     (absento q `(3 . (4 . 5))))
   '((_.0
      :
      (=/= ((_.0 . 3))
           ((_.0 . 4))
           ((_.0 . 5))
           ((_.0 . (3 . (4 . 5))))
           ((_.0 . (4 . 5)))))))
  
  (test
   (run* (x y)
     (symbol x)
     (number y)
     (== x y))
   '())

  (test
   (run* (a b)
     (fresh (x)
       (absento a b)
       (symbol a)
       (number x)
       (== x b)))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (q) (absento 5 q) (absento 5 q))
   '((_.0 : (absento (5 _.0)))))
  
  (test
   (run* (q) (absento 5 q) (absento 6 q))
   '((_.0 : (absento (5 _.0) (6 _.0)))))

  (test
   (run* (q) (absento 5 q) (symbol q))
   '((_.0 : (symbol _.0))))

  (test
   (run* (q) (number q) (absento 'tag q))
   '((_.0 : (number _.0))))

  (test
   (run* (q) (absento 'tag q) (number q))
   '((_.0 : (number _.0))))

  (test
   (run* (q) (== 5 q) (absento 5 q))
   '())

  (test
   (run* (q) (== q `(5 6)) (absento 5 q))
   '())

  (test
   (run* (q) (absento 5 q) (== q `(5 6)))
   '())

  (test
   (run* (q) (absento 5 q) (== 5 q))
   '())
  
  (test
   (run* (q) (absento 'tag1 q) (absento 'tag2 q))
   '((_.0 : (absento (tag1 _.0) (tag2 _.0)))))
  
  (test
   (run* (q) (absento 'tag q) (number q))
   '((_.0 : (number _.0))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a)
     (symbol a)
     (number b))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (a b)
     (absento b a)
     (absento a b)
     (symbol a)
     (symbol b))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))) (symbol _.0 _.1))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a))
   '(((_.0 _.1) : (absento (_.0 _.1) (_.1 _.0)))))

  (test
   (run* (a b)
     (absento 5 a)
     (absento 5 b))
   '(((_.0 _.1) : (absento (5 _.0) (5 _.1)))))

  (test
   (run* (q)
     (fresh (a b c)
       (== `(,a ,b) c)
       (== `(,c ,c) q)
       (symbol b)
       (number c)))
   '())
  
  (test
   (run* (q) (absento 'tag q) (symbol q))
   '((_.0 : (=/= ((_.0 . tag))) (symbol _.0))))

  (test
   (run* (q) (absento 5 q) (number q))
   '((_.0 : (=/= ((_.0 . 5))) (number _.0))))

  (test
   (run* (q)
     (fresh (a)
       (== 5 a) (absento a q)))
   '((_.0 : (absento (5 _.0)))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a)
     (symbol a)
     (symbol b))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))) (symbol _.0 _.1))))

  (test
   (run* (q) (absento '() q))
   '((_.0 : (absento (() _.0)))))

  (test
   (run* (q) (absento `(3 4) q))
   '((_.0 : (absento ((3 4) _.0)))))

  (test
   (run* (q)
     (fresh (d a c)
       (== `(3 . ,d) q)
       (=/= `(,c . ,a) q)
       (== '(3 . 4) d)))
   '((3 3 . 4)))

  (test
   (run* (q)
     (fresh (a)
       (== `(,a . ,a) q)))
   '((_.0 . _.0)))

  (test
   (run* (q)
     (fresh (a b)
       (==  `((3 4) (5 6)) q)
       (absento `(3 4) q)))
   '())
  
  (test
   (run* (q) (absento q 3))
   '((_.0 : (=/= ((_.0 . 3))))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a))
   '(((_.0 _.1) : (absento (_.0 _.1) (_.1 _.0)))))

  (test
   (run* (q)
     (fresh (a b)
       (absento `(,a . ,b) q)
       (== q `(3 . (,b . ,b)))))
   '((3 _.0 . _.0)))

  (test
   (run* (q)
     (fresh (a b)
       (absento `(,a . ,b) q)
       (== q `(,a 3 . (,b . ,b)))))
   '(((_.0 3 _.1 . _.1) : (=/= ((_.0 . _.1))))))
  
  (test
   (run* (q)
     (fresh (a)
       (absento a q)
       (absento q a)))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (a)
       (absento `(,a . 3) q)))
   '(_.0)) 
  
  (test
   (run* (q)
     (fresh (a)
       (absento `(,a . 3) q)))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (a b c d e)
       (absento `((3 4 ,a) (4 ,b) ((,c)) ,d ,e) q)))
   '(_.0))

  (test
   (run* (q) 
     (fresh (a)
       (absento a q)
       (== 5 a)))
   '((_.0 : (absento (5 _.0)))))
  
  (test
   (run* (q) 
     (fresh (a b c d)
       (== a 5)
       (== a b)
       (== b c)
       (absento d q)
       (== c d)))
   '((_.0 : (absento (5 _.0)))))

  (test
   (run* (q) 
     (fresh (a b c d)
       (== a b)
       (== b c)
       (absento a q)
       (== c d)
       (== d 5)))
   '((_.0 : (absento (5 _.0)))))

  (test
   (run* (q)
     (fresh (t1 t2 a)
       (== `(,a . 3) t1)
       (== `(,a . (4 . 3)) t2)
       (== `(,t1 ,t2) q)
       (absento t1 t2)))
   '((((_.0 . 3) (_.0 4 . 3)) : (=/= ((_.0 . 4))))))

  (test
   (run* (q)
     (fresh (a)
       (== `(,a . 3) q)
       (absento q `(,a . (4 . 3)))))
   '(((_.0 . 3) : (=/= ((_.0 . 4))))))

  (test
   (run* (q) 
     (fresh (a d c)
       (== '(3 . 4) d)
       (absento `(3 . 4) q)
       (== `(3 . ,d) q)))
   '())
  
  (test
   (run* (a b)
     (absento a b)
     (absento b a)
     (symbol a)
     (number b))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))
  

  (test
   (run* (q)
     (number q)
     (absento q 3))
   '((_.0 : (=/= ((_.0 . 3))) (number _.0))))
  
  (test
   (run* (q)
     (fresh (a)
       (== `(,a . 3) q)
       (absento q `(,a . (4 . (,a . 3))))))
   '())

  (test
   (run* (q) 
     (fresh (a) 
       (== `(,a . 3) q)
       (absento q `(,a . ((,a . 3) . (,a . 4))))))
   '())
  
  (test
   (run* (q)
     (fresh (a d c)
       (== `(3 . ,d) q)
       (== '(3 . 4) d)
       (absento `(3 . 4) q)))
   '())
  
  (test
   (run* (q)
     (fresh (a b c)
       (symbol b)
       (absento `(,3 . ,a) `(,b . ,c))
       (== `(,a ,b ,c) q)))
   '(((_.0 _.1 _.2)
      : 
      (absento ((3 . _.0) _.2))
      (symbol _.1))))

  (test
   (run* (q) 
     (fresh (a b c) 
       (absento a b)
       (absento b c)
       (absento c q)
       (symbol a)))
   '(_.0))
  
  (test
   (run* (q) 
     (fresh (a b c) 
       (=/= a b)
       (=/= b c)
       (=/= c q)
       (symbol a)))
   '(_.0))
  
  (test
   (run* (q) (symbol q) (== 'tag q))
   '(tag))
  
  (test
   (run* (q) (fresh (b) (absento '(3 4) `(,q ,b))))
   '((_.0 : (absento ((3 4) _.0)))))
  
  (test
   (run* (q) (absento 6 5))
   '(_.0))

  (test
   (run* (q)
     (fresh (a b)
       (=/= a b)
       (symbol a)
       (number b)
       (== `(,a ,b) q)))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (q)
     (fresh (a b c d)
       (=/= `(,a ,b) `(,c ,d))
       (symbol a)
       (number c)
       (symbol b)
       (number c)
       (== `(,a ,b ,c ,d) q)))
   '(((_.0 _.1 _.2 _.3) : (number _.2) (symbol _.0 _.1))))

  (test
   (run* (q) (fresh (a b) (=/= `(,a . 3) `(,b . 3)) (symbol a) (number b) (== `(,a ,b) q)))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a)
     (symbol a)
     (number b))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (a b)
     (symbol a)
     (number b)
     (absento a b)
     (absento b a))
   '(((_.0 _.1) : (number _.1) (symbol _.0))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a)
     (symbol a)
     (symbol b))
   '(((_.0 _.1) : (=/= ((_.0 . _.1))) (symbol _.0 _.1))))

  (test
   (run* (a b)
     (absento a b)
     (absento b a))
   '(((_.0 _.1) : (absento (_.0 _.1) (_.1 _.0)))))

  (test
   (run* (a b)
     (absento b '(1 . 2))
     (absento '(1 . 2) b))
   '(((_.0 _.1)
      :
      (=/= ((_.1 . 1)) ((_.1 . 2)))
      (absento ((1 . 2) _.1)))))

  (test
   (run* (a b)
     (== a '(1 . 2))
     (absento b a)
     (absento a b))
   '((((1 . 2) _.0)
      :
      (=/= ((_.0 . 1)) ((_.0 . 2)))
      (absento ((1 . 2) _.0)))))

  (test
   (run* (a b)
     (absento b a)
     (absento a b)
     (== a '(1 . 2)))
   '((((1 . 2) _.0)
      :
      (=/= ((_.0 . 1)) ((_.0 . 2)))
      (absento ((1 . 2) _.0)))))

  (test
   (run* (q)
     (fresh (a b c)
       (absento a q)
       (absento q a)
       (== `(,b . ,c) a)
       (== '(1 . 2) b)
       (== '(3 . 4) c)))
   '((_.0 
      :
      (=/= ((_.0 . 1)) ((_.0 . 2)) ((_.0 . 3)) ((_.0 . 4))
           ((_.0 . (1 . 2))) ((_.0 . (3 . 4))))
      (absento (((1 . 2) 3 . 4) _.0)))))
  
  (test
   (run* (x y)
     (absento x `(1 . ,y))
     (== '(2 . 3) y)) ;; this line is hard I guess
   '(((_.0 (2 . 3)) 
      :
      (=/= ((_.0 . 1))
           ((_.0 . 2))
           ((_.0 . 3))
           ((_.0 . (1 2 . 3))) ;; missing this
           ((_.0 . (2 . 3)))) 
      )))

  (test
   (run* (q)
     (fresh (a b c d e f g)
       (absento a q)
       (absento q a)
       (== `(,b . ,c) a)
       (== `(,d . ,e) b)
       (== `(,f . ,g) c)
       (== '(1 . 2) d)
       (== '(3 . 4) e)
       (== '(5 . 6) f)
       (== '(7 . 8) g)))
   '((_.0 
      :
      (=/= ((_.0 . 1))
           ((_.0 . 2))
           ((_.0 . 3))
           ((_.0 . 4))
           ((_.0 . 5))
           ((_.0 . 6))
           ((_.0 . 7))
           ((_.0 . 8))
           ((_.0 . (1 . 2)))
           ((_.0 . (3 . 4)))
           ((_.0 . (5 . 6)))
           ((_.0 . (7 . 8)))
           ((_.0 . ((1 . 2) 3 . 4)))
           ((_.0 . ((5 . 6) 7 . 8))))
      (absento ((((1 . 2) 3 . 4) (5 . 6) 7 . 8) _.0)))))

  (test
   (run* (q)
     (absento 3 q)
     (absento '(3 4) q))
   '((_.0 : (absento (3 _.0)))))

  (test
   (run* (q)
     (fresh (x a b)
       (== x `(,a ,b))
       (absento '(3 4) x)
       (absento 3 a)
       (absento 4 b)
       (== q `(,a 2))))
   '(((_.0 2) : (absento (3 _.0)))))

  (test
   (run* (q)
     (fresh (d)
       (== `(3 . ,d) q)
       (absento `(3 . 4) q)
       (== '(3 . 4) d)))
   '())

  (test
   (run* (q)
     (fresh (d)
       (absento `(3 . 4) q)
       (== `(3 . ,d) q)
       (== '(3 . 4) d)))
   '())

  (test
   (run* (q)
     (fresh (d a c)
       (== `(3 . ,d) q)
       (absento `(3 . ,a) q)
       (== c d)
       (== `(3 . ,a) c)))
   '())

  (test
   (run* (q)
     (fresh (a b)
       (absento `(3 . ,a) `(,b . 4))
       (== `(,a . ,b) q)))
   '(((_.0 . _.1) : (=/= ((_.0 . 4) (_.1 . 3))) (absento ((3 . _.0) _.1)))))

  (test
   (run* (q)
     (fresh (d)
       (== `(3 . ,d) q)
       (absento `(3 . 4) q)))
   '(((3 . _.0) : (=/= ((_.0 . 4))) (absento ((3 . 4) _.0)))))

  (test
   (run* (q)
     (fresh (d)
       (== `(3 . ,d) q)
       (== '(3 . 4) d))
     (absento `(3 . 4) q))
   '())
  )

(define (test-absento-long)
  (test-absento))

(module+ main
  (test-absento-long))

