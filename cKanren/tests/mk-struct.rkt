#lang racket/base

(require 
 racket/base 
 "../ck.rkt"
 "../tree-unify.rkt"
 "../tester.rkt")

(provide test-mk-struct test-mk-struct-long)

(define (test-mk-struct)
  (test "sanity test 1"
        (run* (q) succeed)
        '(_.0))
  
  (test "sanity test 2"
        (run* (q) (== 5 5))
        '(_.0))

  (test-check "1" 
              (run* (q) 
                    (fresh (x y)
                      (== q (vector x y))
                      (== y 2)))
              `(#(_.0 2)))
  
  (test-check "2"
              (run* (q)
                    (fresh (x y)
                      (== (vector x 2) (vector 1 y))
                      (== q `(,x ,y))))
              `((1 2)))
  
  (test-check "3"
              (run* (q)
                    (== (vector 1 2) (list 1 2)))
              `())
  
  (struct my-struct (a)
    #:methods gen:mk-struct
    [(define (recur my k) (k (my-struct-a my) `()))
     (define (constructor my) (lambda (a d) (my-struct a)))
     (define (reify-mk-struct my r) 
       `(my-struct ,(reify-term (my-struct-a my) r)))
     (define (override-occurs-check? my) #f)]
    #:methods gen:unifiable
    [(define (compatible? my x s c)
       (or (var? x) (my-struct? x)))
     (define (gen-unify my x p s c e)
       (cond
        [(var? x) (unify p (ext-s x my s) c e)]
        [else (unify-two (my-struct-a my) x p s c e)]))])
  
  (struct my-other-struct my-struct (b)
    #:methods gen:mk-struct
    [(define (recur my k) (k (my-struct-a my) `(,(my-other-struct-b my))))
     (define (constructor my) (lambda (a d) (my-other-struct a (car d))))
     (define (reify-mk-struct my r)
       `(my-struct ,(reify-term (my-struct-a my) r)))
     (define (override-occurs-check? my) #f)]
    #:methods gen:unifiable
    [(define (compatible? my x s c)
       (or (var? x) (my-other-struct? x)))
     (define (gen-unify my x p s c e)
       (cond
        [(var? x) (unify p (ext-s x my s) c e)]
        [else 
         (let ([my-a (my-struct-a my)]
               [x-a  (my-struct-a x)]
               [my-b (my-other-struct-b my)]
               [x-b  (my-other-struct-b x)])
           (unify-two my-a x-a `((,my-b . ,x-b) . ,p) s c e))]))])
  
  (test-check "4" (run* (q) (== q (my-struct 'x))) `((my-struct x)))
  (test-check "5" (run* (q) (== q (my-other-struct 'x 'y))) `((my-struct x)))

  (test-check "5.1" 
              (run* (q)
                (fresh (x y)
                  (== (my-other-struct x 2)
                      (my-other-struct 1 y))
                  (== q `(,x ,y))))
              `((1 2)))
  
  (test-check "6" 
              (run* (q) (== (my-struct 'x) (my-other-struct 'x 'y)))
              `())
  
  (test-check "7" 
              (run* (q) (== (my-other-struct 'x 'y) (my-struct 'x)))
              `())
  
  (void))

(define (test-mk-struct-long)
  (test-mk-struct))

(module+ main
  (test-mk-struct))
