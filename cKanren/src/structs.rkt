#lang racket/base

(require racket/generic
         "helpers.rkt"
         "infs.rkt")

(require (for-syntax racket/base))

 ;; variables
(provide (struct-out var) define-var-type cvar->str)

;; goals
(provide (struct-out goal) lambdag@ lambdag@/private)

;; == VARIABLES ================================================================

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(define-generics cvar (cvar->str cvar))

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct var (x) 
  #:methods gen:cvar 
  [(define (cvar->str x) "_")]
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-var args))])

(define-syntax-rule (define-var-type name str rest ...)
  (struct name var () rest ...
    #:methods gen:cvar
    [(define (cvar->str x) str)]
    #:methods gen:custom-write
    [(define (write-proc . args) (apply write-var args))]))

;; write-var controls how variables are displayed
(define (write-var var port mode)
  ((parse-mode mode) (format "#~a(~s)" (cvar->str var) (var-x var)) port))

;; == GOALS ====================================================================

;; a goal is just a function that can be applied to a's
(struct goal (fn) 
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<goal>" port)]))

;; macro to return a goal with the specified function
(define-syntax lambdag@
  (syntax-rules ()
    [(_ (a) e ...) 
     (lambdag@/private (a) e ...)]
    [(_ (a : s) e ...)
     (lambdag@/private (a) 
       (let ([s (substitution-s (a-s a))])
         e ...))]
    [(_ (a : s c) e ...)
     (lambdag@/private (a) 
       (let ([s (substitution-s (a-s a))]
             [c (constraint-store-c (a-c a))])
         e ...))]))

;; internal macro that can also divide the package into the queue and the tree
(define-syntax lambdag@/private
  (syntax-rules ()
    [(_ (a) e ...)
     (goal (lambda (a) e ...))]
    [(_ (a div s c q t) e ...)
     (lambdag@/private (a)
         (let ([s (a-s a)]
               [c (a-c a)]
               [q (a-q a)] 
               [t (a-t a)])
           e ...))]))


