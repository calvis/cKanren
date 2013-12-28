#lang racket

(require "constraint-store.rkt" "substitution.rkt" "queue.rkt" 
         "debugging.rkt" "infs.rkt" "events.rkt")

(provide (struct-out path))

(provide (all-from-out "constraint-store.rkt"))
(provide (all-from-out "substitution.rkt"))
(provide (all-from-out "queue.rkt"))
(provide (all-from-out "debugging.rkt"))
(provide empty-a)

(provide 
 #;
 (contract-out
  [make-a
   (-> (flat-contract substitution?)
       (flat-contract constraint-store?)
       any/c
       any/c
       (flat-contract event?)
       (flat-contract a?))])
 make-a)

;; == PACKAGE ==================================================================

;; the empty package
(define empty-a 
  (make-a/internal empty-s empty-c empty-q empty-t empty-e))

(define make-a make-a/internal)

