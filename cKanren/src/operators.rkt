#lang racket

(require "helpers.rkt"
         "infs.rkt"
         "structs.rkt"
         "errors.rkt"
         racket/stxparam)

(require 
 (for-syntax "helpers.rkt"
             "errors.rkt"
             syntax/parse))

;; goals and operators
(provide succeed fail conde fresh fresh-aux conj mzerog unitg)

;; impure operators, and other things
(provide ifu condu ifa conda project onceo)

;; debugging
(provide debug debug-conde prt prtm prtt)

;; the failure value
(define mzerog (mzerof))

;; the identity goal
(define unitg (lambdag@ (a) a))

;; applies a goal to an a-inf and returns an a-inf
(define bindg
  (lambda (a-inf g)
    (case-inf a-inf
      [() (mzerof)]
      [(f) (delay (bindg (f) g))]
      [(a) (app-goal g a)]
      [(a f) (mplusg (app-goal g a) (delay (bindg (f) g)))])))

;; performs a conjunction over goals applied to an a-inf
(define-syntax bindg*
  (syntax-rules ()
    [(_ a-inf) a-inf]
    [(_ a-inf g g* ...)
     (bindg* (bindg a-inf g) g* ...)]))

;; combines a-inf and f, returning an a-inf
(define mplusg
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (delay (mplusg (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (delay (mplusg (f) f^)))))))

;; shorthand for combining a-infs
(define-syntax mplusg*
  (syntax-rules ()
    ((_ a-inf) a-inf)
    ((_ a-inf a-inf* ...)
     (mplusg a-inf (delay (mplusg* a-inf* ...))))))

;; shorthand for conjunction
(define-syntax conj
  (syntax-rules ()
    [(_ g) g]
    [(_ g g* ...)
     (lambdag@ (a)
       (delay (bindg* (app-goal g a) g* ...)))]))

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

(define-syntax (app-goal x)
  (syntax-case x ()
    [(_ g a) #`((wrap-goal g #,(build-srcloc-stx #'g)) a)]))

(define (non-goal-error-msg val)
  (string-append
   "expression evaluated to non-goal where a goal was expected"
   (format "\n  value: ~s" val)))

(define (wrap-goal val src)
  (cond
   [(goal? val) val]
   [(format-source src) => 
    (lambda (loc) (error loc (non-goal-error-msg val)))]
   [else (error (non-goal-error-msg val))]))

;; =============================================================================

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
       #'(lambdag@ (a : s c q t) 
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
     (ifu ((app-goal g0 a) g ...)
          ((app-goal g1 a) g^ ...) ...))))

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
  (lambdag@-external (a : s)
    (let ((x (walk* x s)) ...)
      ((conj g g* ...) a))))

;; succeed and fail are the simplest succeeding and failing goals
(define succeed unitg)
(define fail    (lambdag@ (a) mzerog))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.

(define prt  
  (lambdag@ (a) (begin (printf "~a\n" a) a)))
(define (prtm . m) 
  (lambdag@ (a) (begin (apply printf m) a)))

(define (prtt . m) 
  (lambdag@/private (a : s c q t) 
    (begin (display t) (display " ") (apply printf m) a)))

