#lang racket

(require 
 "../ck.rkt"
 "../tree-unify.rkt"
 "../pref.rkt"
 "../tester.rkt")

(provide test-pref test-pref-long)

(define (test-pref)
  (test-check "pref 1"
              (run* (q) (prefo q '(1 2 3)))
              `(1))
  (test-check "pref 2"
              (run* (q) (prefo q '(1 2 3)) (== q 3))
              `(3))
  (test-check "pref 3"
              (run* (q) (prefo q '(1 2 3)) (== q 4))
              `()))

(define (test-pref-long)
  (test-pref))

(module+ main
  (test-pref-long))
