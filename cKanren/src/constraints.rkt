#lang racket

(require "helpers.rkt" "package.rkt")

(provide (all-defined-out))

;; == CONSTRAINTS ==============================================================

(struct constraint (fn)
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<constraint>" port)]))

;; splitting up the package
(define-syntax lambdam@/private
  (syntax-rules (:)
    [(_ (a) e ...)
     (constraint (lambda (a) e ...))]
    [(_ (a : s c q t) e ...)
     (lambdam@/private (a) 
       (let ([s (a-s a)] 
             [c (a-c a)]
             [q (a-q a)]
             [t (a-t a)])
         e ...))]))

(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambdam@/private (a) e ...)]
    [(_ (a : s) e ...)
     (lambdam@/private (a) 
       (let ([s (substitution-s (a-s a))]) 
         e ...))]
    [(_ (a : s c) e ...)
     (lambdam@/private (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
         e ...))]))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; the simplest failing constraint
(define mzerom (lambdam@ (a) #f))

;; applies a constraint to a package
(define (bindm a fm) (fm a))

;; composes two constraints together
(define (composem . fm*)
  (lambdam@ (a)
    (cond
     [(null? fm*) a]
     [((car fm*) a)
      => (apply composem (cdr fm*))]
     [else #f])))

