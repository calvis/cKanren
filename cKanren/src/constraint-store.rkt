#lang racket/base

(require "helpers.rkt" "ocs.rkt")

(provide (all-defined-out))

;; == CONSTRAINT STORE =========================================================

;; wrapper for a constraint store
(struct constraint-store (c)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-constraint-store args))])

;; writes a constraint store
(define (write-constraint-store constraint-store port mode)
  (define fn (lambda (s) ((parse-mode mode) s port)))
  (define c (constraint-store-c constraint-store))
  (fn "#c[")
  (let ([f (lambda (key ocs) (for ([oc ocs]) (fn " ") (fn oc)))])
    (hash-for-each c f))
  (unless (null? c) (fn " "))
  (fn "]"))

;; an empty constraint store
(define empty-c (hasheq))

;; extends the constraint store c with oc
(define (ext-c oc c) 
  (hash-update c (oc-rator oc) (lambda (ocs) (cons oc ocs)) '()))

(define (ext-c* ocs c)
  (for/fold ([c c]) ([oc ocs]) (ext-c oc c)))

;; checks if oc is in c
(define (memq-c oc c)
  (let ([ocs (filter/rator (oc-rator oc) c)])
    (memq oc ocs)))

;; removes oc from c
(define (remq-c oc c) 
  (hash-update c (oc-rator oc) (lambda (ocs) (remq oc ocs)) '()))

;; removes all ocs in oc* from c
(define (remq*-c oc* c)
  (for/fold ([c c]) ([oc oc*]) (remq-c oc c)))

;; filters the constraint store
(define (filter/rator key c)
  (unless (hash? c)
    (error 'filter/rator "not given a c ~s\n" c))
  (hash-ref c key '()))

(define (filter-not/rator sym c)
  (unless (hash? c)
    (error 'filter-not/rator "not given a c ~s\n" c))
  (apply append (for/list ([key (remq sym (hash-keys c))]) (hash-ref c key '()))))

(define (filter-memq/rator symls c)
  (unless (hash? c)
    (error 'filter-memq/rator "not given a c ~s\n" c))
  (apply append (for/list ([key symls]) (hash-ref c key '()))))

(define (filter-not-memq/rator symls c)
  (unless (hash? c)
    (error 'filter-not-memq/rator "not given a c ~s\n" c))
  (apply append (for/list ([key (hash-keys c)])
                          (cond
                           [(memq key symls) '()]
                           [else (hash-ref c key '())]))))

(define (c->list c)
  (apply append (hash-values c)))

