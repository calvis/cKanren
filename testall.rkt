#lang racket

(require "tests/fdtests.rkt"
         "tests/neqtests.rkt"
         "tests/comptests.rkt"
         "tests/nevertruetests.rkt"
         "tests/preftests.rkt"
         "tests/aktests.rkt"
         "tests/mk-struct.rkt")

(run-fdtests)
(run-neqtests)
(run-comptests)
(run-nevertruetests)
(run-preftests)
(run-aktests)
(run-mk-struct-tests)
