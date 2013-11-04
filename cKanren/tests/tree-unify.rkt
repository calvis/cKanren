#lang racket

(require "../ck.rkt"
         "../tester.rkt"
         "../tree-unify.rkt")

(provide test-tree-unify)

(define (test-tree-unify)
  (test (run* (q) (== 5 6)) '())
  (test (run* (q) (== 5 5)) '(_.0))
  
  (test (run 1 (q) (== q 5)) '(5))
  (test (run* (q) (== q 5)) '(5))
  
  (test (run* (q) (== q '(1 2))) 
        '((1 2)))
  
  (test (run* (x y) (== `(,x 1) `(2 ,y)))
        '((2 1)))
)

(module+ main
  (test-tree-unify))
