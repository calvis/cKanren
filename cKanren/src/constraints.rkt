#lang racket

(require "helpers.rkt" "substitution.rkt" "constraint-store.rkt" "infs.rkt" "errors.rkt")

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

#;
(define-syntax (constraint-wrap stx)
  (syntax-parse
    [(constraint-wrap
      (~seq #:package ....)
      (~seq #:event e))]))

;; the failure value
(define mzerom (mzerof))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; succeed and fail are the simplest succeeding and failing constraint
(define succeed identitym)
(define fail    (lambdam@ (a) mzerom))

;; applies a goal to an a-inf and returns an a-inf
(define bindm
  (lambda (a-inf g)
    (case-inf a-inf
      [() (mzerof)]
      [(f) (delay (bindm (f) g))]
      [(a) (app-goal g a)]
      [(a f) (mplusm (app-goal g a) (delay (bindm (f) g)))])))

;; performs a conjunction over goals applied to an a-inf
(define-syntax bindm*
  (syntax-rules ()
    [(_ a-inf) a-inf]
    [(_ a-inf g g* ...)
     (bindm* (bindm a-inf g) g* ...)]))

;; combines a-inf and f, returning an a-inf
(define mplusm
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (delay (mplusm (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (delay (mplusm (f) f^)))))))

;; shorthand for combining a-infs
(define-syntax mplusm*
  (syntax-rules ()
    ((_ a-inf) a-inf)
    ((_ a-inf a-inf* ...)
     (mplusm a-inf (delay (mplusm* a-inf* ...))))))

(define-syntax (app-goal x)
  (syntax-case x ()
    [(_ g a) #`((wrap-goal g #,(build-srcloc-stx #'g)) a)]))

(define (non-goal-error-msg val)
  (string-append
   "expression evaluated to non-constraint where a constraint was expected"
   (format "\n  value: ~s" val)))

(define (wrap-goal val src)
  (cond
   [(constraint? val) val]
   [(format-source src) => 
    (lambda (loc) (error loc (non-goal-error-msg val)))]
   [else (error (non-goal-error-msg val))]))

(define-syntax-rule (start a g g* ...)
  (bindm* (app-goal g a) g* ...))

