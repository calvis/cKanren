#lang racket/base

(require racket/generic)
(require "helpers.rkt")

(provide (struct-out var) define-var-type cvar->str)

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

