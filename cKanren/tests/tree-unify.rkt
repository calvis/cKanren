#lang racket

(require "../ck.rkt"
         "../tester.rkt"
         "../tree-unify.rkt")

(test (run 1 (q) succeed) '(_.0))
(test (run 1 (q) fail) '())

(test (run* (q) succeed) '(_.0))
(test (run* (q) fail) '())

(test (run* (q) (== 5 6)) '())
(test (run* (q) (== 5 5)) '(_.0))

(test (run 1 (q) (== q 5)) '(5))
(test (run* (q) (== q 5)) '(5))

(test (run* (q) (== q '(1 2))) 
      '((1 2)))

(test (run* (x y) (== `(,x 1) `(2 ,y)))
      '((2 1)))
