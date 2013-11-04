#lang racket

(require 
 "tests/absento.rkt"
;;  "tests/ak.rkt"
;;  "tests/comp.rkt"
;;  "tests/fd.rkt"
;;  "tests/framework.rkt"
;;  "tests/infer.rkt"
;;  "tests/interp.rkt"
;;  "tests/mk-struct.rkt"
;;  "tests/mk.rkt"
 "tests/neq.rkt"
 "tests/numbero.rkt"
;;  "tests/no-closure.rkt"
;;  "tests/quines.rkt"
;;  "tests/sets.rkt"
 "tests/symbolo-numbero.rkt"
 "tests/symbolo.rkt"
 "tests/tree-unify.rkt"
)

(define (run-all)
  (test-tree-unify)
;;   (test-mk)
;; 
  (test-absento)
;;   (test-ak)
;;   (test-fd)
;;   (test-infer)
;;   (test-interp)
;;   (test-mk-struct)
  (test-neq)
  (test-number)
;;   (test-no-closure)
;;   (test-quines)
;;   (test-sets)
  (test-symbol)
  (test-symbol-number)
;;   (test-comp)
)

(define (run-all-long)
;;   (test-mk-long)
;; 
;;   (test-absento-long)
;;   (test-ak-long)
;;   (test-fd-long)
;;   (test-infer-long)
;;   (test-interp-long)
;;   (test-mk-struct-long)
;;   (test-neq-long)
;;   (test-number-long)
;;   (test-no-closure-long)
;;   (test-sets-long)
;;   (test-symbol-long)
;;   (test-symbol-number-long)
;;   (test-comp-long)
;; 
;;   (test-quines-long)
  (void)
)

(module+ main (run-all))

(module+ test (run-all-long))


