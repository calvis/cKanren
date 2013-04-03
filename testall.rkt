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

