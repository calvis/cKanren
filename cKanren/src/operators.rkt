#lang racket

(require "helpers.rkt"
         "infs.rkt"
         "errors.rkt"
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

;; succeed and fail are the simplest succeeding and failing ct
(define succeed (lambda@ (a) a))
(define fail    (lambda@ (a) mzerom))

(define onceo (lambda (g) (condu (g))))

(define (succeed-iff bool)
  (if bool succeed fail))

;; =============================================================================

;; shorthand for conjunction
(define-syntax conj
  (syntax-rules ()
    [(_ g) g]
    [(_ g g* ...)
     (lambda@ (a) (delay (start a g g* ...)))]))

(define-syntax disj
  (syntax-rules ()
    [(_ g) g]
    [(_ g g* ...)
     (conde [g] [g*] ...)]))

(define-syntax-parameter conde
  (lambda (stx)
    (syntax-parse stx
      [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
       (cond
         [(expand-debug?)
          (with-syntax ([(branches ...) (attribute branch-name)])
            #'(debug-conde [#:name branches g g* ...] ...))]
         [else 
          #'(lambda@ (a) 
              (delay (mplusm* (start a g g* ...) ...)))])])))

(define-syntax (debug-conde stx)
  (syntax-parse stx
    [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
     (with-syntax ([(labels ...) (attribute branch-name)])
       #'(lambda@ (a [s c q t e])
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
  (lambda@ (a)
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
  (lambda@ (a)
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
  (lambda@ (a : s)
    (let ((x (walk*-internal x s)) ...)
      (bindm a (conj g g* ...)))))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.

(define prt  
  (lambda@ (a) (begin (printf "~a\n" a) a)))

(require racket/pretty)
(define pprt
  (lambda@ (a [s c q t e])
    (begin (pretty-print a) a)))

(define (prtm . m) 
  (lambda@ (a) (begin (apply printf m) a)))

(define (prtt . m) 
  (lambda@ (a [s c q t e]) 
    (begin (display t) (display " ") (apply printf m) a)))

(define diaf
  (lambda@ (a) (error 'diaf "dying: ~s" a)))

(define-syntax-rule (for/disj (for-clause ...) body)
  (for/fold ([ct fail]) (for-clause ...)
    (disj body ct)))

(define-syntax-rule (for/conj (for-clause ...) body)
  (for/fold ([ct succeed]) (for-clause ...)
    (conj body ct)))
