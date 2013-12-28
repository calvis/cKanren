#lang racket

(require "operators.rkt")

(provide empty-q empty-q? ext-q)

;; == QUEUE ====================================================================

;; an empty queue 
(define empty-q succeed)
(define empty-q? ((curry eq?) empty-q))

(define (ext-q q q^) (conj q q^))

