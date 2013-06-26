#lang racket

(require "helpers.rkt"
         "infs.rkt"
         "errors.rkt"
         "goals.rkt"
         "variables.rkt"
         "mk-structs.rkt"
         "debugging.rkt"
         "constraints.rkt"
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
     (lambdam@ (a) (delay (start a g g* ...)))]))

#;
(define-syntax disj
  (syntax-rules ()
    [(_ g) g]
    [(_ g* ...+)
     (lambdam@ (a)
       (delay (mplusm* (app-goal g* a) ...)))]))

(define-syntax-parameter conde
  (lambda (stx)
    (syntax-parse stx
      [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
       (cond
         [(expand-debug?)
          (with-syntax ([(branches ...) (attribute branch-name)])
            #'(debug-conde [#:name branches g g* ...] ...))]
         [else 
          #'(lambdam@ (a) 
              (delay (mplusm* (start a g g* ...) ...)))])])))

(define-syntax (debug-conde stx)
  (syntax-parse stx
    [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
     (with-syntax ([(labels ...) (attribute branch-name)])
       #'(lambdam@/private (a : s c q t) 
           (delay 
            (mplusm* 
             (let ([a (make-a s c q (add-level t 'labels))])
               (start a g g* ...))
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
  (lambdam@ (a)
    (delay (ifa ((app-goal g0 a) g ...) 
                ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifa
  (syntax-rules ()
    ((_) mzerom)
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (delay (loop (f))))
         ((a) (bindm* a-inf g ...))
         ((a f) (bindm* a-inf g ...)))))))

(define-syntax-rule (condu (g0 g ...) (g1 g^ ...) ...)
  (lambdam@ (a)
    (delay
     (ifu ((start a g0) g ...)
          ((start a g1) g^ ...) ...))))

(define-syntax ifu
  (syntax-rules ()
    ((_) mzerom)
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (delay (loop (f))))
         ((a) (bindm* a-inf g ...))
         ((a f) (bindm* a g ...)))))))

(define-syntax-rule (project (x ...) g g* ...) 
  (lambdam@ (a : s)
    (let ((x (walk* x s)) ...)
      ((conj g g* ...) a))))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.

(define prt  
  (lambdam@ (a) (begin (printf "~a\n" a) a)))
(define (prtm . m) 
  (lambdam@ (a) (begin (apply printf m) a)))

(define (prtt . m) 
  (lambdam@/private (a : s c q t) 
    (begin (display t) (display " ") (apply printf m) a)))

