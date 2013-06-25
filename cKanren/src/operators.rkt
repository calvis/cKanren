#lang racket

(require "helpers.rkt"
         "infs.rkt"
         "errors.rkt"
         "goals.rkt"
         "variables.rkt"
         "mk-structs.rkt"
         "debugging.rkt"
         racket/stxparam)

(require 
 (for-syntax "helpers.rkt"
             "errors.rkt"
             syntax/parse))

(provide (all-defined-out))

;; defines a macro to create new unconstrained variables
(define-syntax fresh-aux
  (syntax-rules ()
    [(_ constructor (x ...) g g* ...)
     (let ([x (constructor 'x)] ...)
       (conj g g* ...))]))

;; miniKanren's "fresh" defined in terms of fresh-aux over vars
(define-syntax-rule (fresh (x ...) g g* ...)
  (fresh-aux var (x ...) g g* ...))

(define onceo (lambda (g) (condu (g))))

;; =============================================================================

;; shorthand for conjunction
(define-syntax conj
  (syntax-rules ()
    [(_ g) g]
    [(_ g g* ...)
     (lambdag@ (a) (delay (start a g g* ...)))]))

(define-syntax-parameter conde
  (lambda (stx)
    (syntax-parse stx
      [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
       (cond
         [(expand-debug?)
          (with-syntax ([(branches ...) (attribute branch-name)])
            #'(debug-conde [#:name branches g g* ...] ...))]
         [else 
          #'(lambdag@ (a) 
              (delay (mplusg* (bindg* (app-goal g a) g* ...) ...)))])])))

(define-syntax (debug-conde stx)
  (syntax-parse stx
    [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
     (with-syntax ([(labels ...) (attribute branch-name)])
       #'(lambdag@/private (a : s c q t) 
           (delay 
            (mplusg* 
             (let ([a (make-a s c q (add-level t 'labels))])
               (bindg* (app-goal g a) g* ...))
             ...))))]))

(define-syntax (debug stx)
  (syntax-parse stx
    [(debug #:on)
     (begin (expand-debug? #t) #'(debug? #t))]
    [(debug #:off)
     (begin (expand-debug? #f) #'(debug? #f))]
    [(debug expr ...+)
     #'(syntax-parameterize 
        ([conde (... (syntax-rules ()
                       ([_ clauses ...]
                        (debug-conde clauses ...))))])
        (parameterize ([debug? #t])
          expr ...))]))

(define-syntax-rule (conda (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (delay (ifa ((app-goal g0 a) g ...) 
                ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifa
  (syntax-rules ()
    ((_) mzerog)
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (delay (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a-inf g ...)))))))

(define-syntax-rule (condu (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (delay
     (ifu ((start a g0) g ...)
          ((start a g1) g^ ...) ...))))

(define-syntax ifu
  (syntax-rules ()
    ((_) mzerog)
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (delay (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a g ...)))))))

(define-syntax-rule (project (x ...) g g* ...) 
  (lambdag@ (a : s)
    (let ((x (walk* x s)) ...)
      ((conj g g* ...) a))))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.

(define prt  
  (lambdag@ (a) (begin (printf "~a\n" a) a)))
(define (prtm . m) 
  (lambdag@ (a) (begin (apply printf m) a)))

(define (prtt . m) 
  (lambdag@/private (a : s c q t) 
    (begin (display t) (display " ") (apply printf m) a)))

