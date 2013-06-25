#lang racket/base

(require "constraint-store.rkt" "substitution.rkt" "queue.rkt" 
         "debugging.rkt" "infs.rkt")

(provide (struct-out a)
         (struct-out substitution)
         (struct-out path)
         (struct-out constraint-store))

(provide (all-from-out "constraint-store.rkt"))
(provide (all-from-out "substitution.rkt"))
(provide (all-from-out "queue.rkt"))
(provide (all-from-out "debugging.rkt"))
(provide (struct-out a))
(provide empty-a)

;; == PACKAGE ==================================================================

;; the empty package
(define empty-a 
  (make-a (substitution empty-s)
          (constraint-store empty-c)
          empty-q
          empty-t))

