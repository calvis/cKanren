#lang racket/base

(require racket/generic racket/vector)
(require "substitution.rkt" "variables.rkt" "events.rkt")

(provide (all-defined-out))

;; =============================================================================

(define-generics mk-struct
  ;; recur allows generic traversing of mk-structs.  k should be a
  ;; procedure expecting two arguments, the first thing to process,
  ;; and a list of remaining things to process.
  (recur mk-struct k)

  ;; returns a function that will create a new mk-struct given
  ;; arguments like the arguments to k
  (constructor mk-struct)

  ;; for reification 
  (reify-mk-struct mk-struct r)

  ;; structs also have the option of overriding the occurs-check for
  ;; variables if it's okay to unify a variable to a struct with the
  ;; same variable inside (ex. sets)
  (override-occurs-check? mk-struct)

  #:fallbacks
  [(define (override-occurs-check? mk) #f)]

  #:defaults
  ([pair?
    (define (recur p k)
      (k (car p) (cdr p)))
    (define (constructor p) cons)
    (define (reify-mk-struct p r)
      (reify-pair p r))]
   [vector?
    (define (recur v k)
      (let ([v (vector->list v)])
        (k (car v) (cdr v))))
    (define (constructor v)
      (compose list->vector cons))
    (define (reify-mk-struct v r)
      (reify-vector v r))]))

(define (reify-term t r)
  (cond
   [(mk-struct? t)
    (reify-mk-struct t r)]
   [else (walk/internal t r #f)]))

(define (default-mk-struct? x)
  (or (pair? x) (vector? x)))

(define (same-default-type? x y)
  (or (and (pair? x) (pair? y))
      (and (vector? x) (vector? y))))

(define (reify-pair p r)
  (cons (reify-term (car p) r)
        (reify-term (cdr p) r)))

(define (reify-vector v r)
  (vector-map (lambda (t) (reify-term t r)) v))

;; returns #t if p contains any variables
(define (any/var? x)
  (cond
   ((mk-struct? x)
    (recur x (lambda (a d) (or (any/var? a) (any/var? d)))))
   (else (var? x))))

;; returns #t if t constains variables in x*
(define (any-relevant/var? t x*)
  (cond
   ((mk-struct? t)
    (recur t (lambda (a d) (or (any-relevant/var? a x*)
                               (any-relevant/var? d x*)))))
   (else (and (var? t) (memq t x*)))))

(define (filter*/var? t)
  (cond
   [(var? t) `(,t)]
   [(mk-struct? t)
    (define (k a d) 
      (append (filter*/var? a)
              (filter*/var? d)))
    (recur t k)]
   [else `()]))

;; walks an entire mk-struct
(define walk*
  (case-lambda
   [(u s)
    (define v (walk u s))
    (cond
     [(mk-struct? v)
      (define (k a d) 
        ((constructor v) (walk* a s) (walk* d s)))
      (recur v k)]
     [else v])]
   [(u s c e)
    (define v (walk u s c e))
    (cond
     [(mk-struct? v)
      (define (k a d) 
        ((constructor v) (walk* a s c e) (walk* d s c e)))
      (recur v k)]
     [else v])]))

