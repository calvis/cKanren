#lang s-exp "../ck-lang.rkt"

(require racket/base "tester.rkt" "../tree-unify.rkt")
(provide run-mk-struct-tests)

(define (run-mk-struct-tests)
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
     (define (unifiable? my x) #t)
     (define (mk-struct->sexp my) `(my-struct ,(my-struct-a my)))])
  
  (struct my-other-struct my-struct (b)
    #:methods gen:mk-struct
    [(define (recur my k) (k (my-struct-a my) `(,(my-other-struct-b my))))
     (define (constructor my) (lambda (a d) (my-other-struct a (car d))))
     (define (unifiable? my x) (my-other-struct? x))
     (define (mk-struct->sexp my) `(my-struct ,(my-struct-a my)))])
  
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

(module+ main
  (run-mk-struct-tests))
