#lang racket

(require "helpers.rkt" "infs.rkt" "errors.rkt" "substitution.rkt" "constraint-store.rkt")
(require (for-syntax "helpers.rkt" "errors.rkt" syntax/parse))

(provide (all-defined-out))

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

;; the failure value
(define mzerog (mzerof))

;; the identity goal
(define unitg (lambdag@ (a) a))

;; succeed and fail are the simplest succeeding and failing goals
(define succeed unitg)
(define fail    (lambdag@ (a) mzerog))

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

(define-syntax-rule (start a g g* ...)
  (bindg* (app-goal g a) g* ...))

