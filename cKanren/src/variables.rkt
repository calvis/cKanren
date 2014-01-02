#lang racket

(require racket/generic (for-syntax syntax/parse racket/syntax))
(require "helpers.rkt")

(provide cvar? var var? var-x define-cvar-type define-var-type reify-n reified-var?)

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(struct cvar (str x)
        #:methods gen:custom-write 
        [(define (write-proc . args) (apply write-cvar args))])

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct -var cvar ())
(define (var x) (-var "_" x))
(define (var? x) (-var? x))
(define var-x cvar-x)

(define-syntax (define-cvar-type stx)
  (syntax-parse stx
    [(define-cvar-type name str rest ...)
     (define/with-syntax name? 
       (format-id #'name "~a?" (syntax-e #'name)))
     #'(begin
         (struct -name cvar () rest ...)
         (define (name x) (-name str x))
         (define name? -name?))]))

(define-syntax (define-var-type stx)
  (syntax-parse stx
    [(define-var-type name str rest ...)
     (define/with-syntax name? 
       (format-id #'name "~a?" (syntax-e #'name)))
     #'(begin
         (struct -name -var () rest ...)
         (define (name x) (-name str x))
         (define name? -name?))]))

;; write-var controls how variables are displayed
(define (write-cvar var port mode)
  ((parse-mode mode) (format "#~a(~s)" (cvar-str var) (cvar-x var)) port))

(define (reified-var? v)
  (and (symbol? v)
       (match (string->list (symbol->string v))
         [(list #\_ #\. n) (number? n)]
         [else #f])))

(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar-str cvar) (number->string n))))

