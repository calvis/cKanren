#lang racket

(require 
 "tests/absento.rkt"
 "tests/ak.rkt"
 "tests/comp.rkt"
 "tests/fd.rkt"
 "tests/infer.rkt"
 "tests/interp.rkt"
 "tests/mk-struct.rkt"
 "tests/mk.rkt"
 "tests/neq.rkt"
 "tests/nevertrue.rkt"
 "tests/numbero.rkt"
 "tests/no-closure.rkt"
 "tests/pref.rkt"
 "tests/quines.rkt"
 "tests/symbolo-numbero.rkt"
 "tests/symbolo.rkt"
)

(define (run-all)
  (test-absento)
  (test-ak)
  (test-comp)
  (test-fd)
  (test-infer)
  (test-interp)
  (test-mk-struct)
  (test-mk)
  (test-neq)
  (test-nevertrue)
  (test-numbero)
  (test-no-closure)
  (test-pref)
  (test-quines)
  (test-symbolo)
  (test-symbolo-numbero)
)

(define (run-all-long)
  (test-absento-long)
  (test-ak-long)
  (test-comp-long)
  (test-fd-long)
  (test-infer-long)
  (test-interp-long)
  (test-mk-struct-long)
  (test-mk-long)
  (test-neq-long)
  (test-nevertrue-long)
  (test-numbero-long)
  (test-no-closure-long)
  (test-pref-long)
  (test-quines-long)
  (test-symbolo-long)
  (test-symbolo-numbero-long)
)

(module+ main
  (run-all))

(module+ test
  (run-all-long))


