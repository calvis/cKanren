#lang racket

(require "helpers.rkt" "substitution.rkt" "constraint-store.rkt" "infs.rkt" "errors.rkt")
(require (for-syntax syntax/parse racket/syntax))

(provide lambdam@ lambdam@/private mzerom identitym succeed fail 
         bindm bindm* mplusm mplusm* start app-goal #%app-safe)

;; == CONSTRAINTS ==============================================================

(struct constraint (fn)
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<constraint>" port)]))

;; splitting up the package
(define-syntax lambdam@/private
  (syntax-rules (:)
    [(_ (a) body ...)
     (constraint (lambda (a [e #f]) body ...))]
    [(_ (a e) body ...)
     (constraint (lambda (a [e #f]) body ...))]
    [(_ (a : s c q t) body ...)
     (lambdam@/private (a) 
       (let ([s (a-s a)] 
             [c (a-c a)]
             [q (a-q a)]
             [t (a-t a)])
         body ...))]))

(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) body ...) 
     (lambdam@/private (a) body ...)]
    [(_ (a : s) body ...)
     (lambdam@/private (a) 
       (let ([s (substitution-s (a-s a))]) 
         body ...))]
    [(_ (a : s c) body ...)
     (lambdam@/private (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
         body ...))]
    [(_ (a : s c e) body ...)
     (lambdam@/private (a e) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
         body ...))]))

;; the failure value
(define mzerom (mzerof))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; succeed and fail are the simplest succeeding and failing constraint
(define succeed identitym)
(define fail    (lambdam@ (a) mzerom))

;; applies a goal to an a-inf and returns an a-inf
(define bindm
  (lambda (a-inf g [e #f])
    (case-inf a-inf
      [() (mzerof)]
      [(f) (delay (bindm (f) g e))]
      [(a) (app-goal g a e)]
      [(a f) (mplusm (app-goal g a e) (delay (bindm (f) g e)))])))

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

#;
(define-syntax (app-goal x)
  (syntax-case x ()
    [(_ g a) #`((wrap-goal g #,(build-srcloc-stx #'g)) a)]))

(define-syntax app-goal
  (syntax-rules ()
    [(_ g a) (g a)]
    [(_ g a e) (g a e)]))

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

;; This is a version of application that will catch when users have
;; misplaced goals.

;; If the user is trying to apply a goal to something that is not a
;; package, or trying to apply a goal to zero or many things, they
;; will get an goal-as-fn-exn.  This will fix the stupid "incorrect
;; number of arguments to #<procedure>" errors.

(struct exn:goal-as-fn exn:fail ())
(define (raise-goal-as-fn-exn src)
  (raise
   (exn:goal-as-fn
    (format "~s: goal applied as a procedure" (format-source src))
    (current-continuation-marks))))

;; The only correct application of a goal g is to a package a; i.e. (g a).
(define-for-syntax (valid-app?-pred fn args) 
  (syntax-case args ()
    [(a) #`(or (not (constraint? #,fn)) (a? a))]
    [(a* ...) #`(not (constraint? #,fn))]))

(define-syntax (#%app-safe x)
  (syntax-case x () 
    [(_ fn arg ...)
     (with-syntax* ([(fn^ arg^ ...) 
                     (generate-temporaries #'(fn arg ...))]
                    [src (build-srcloc-stx #'fn)]
                    [valid-app? (valid-app?-pred #'fn^ #'(arg^ ...))])
       (syntax/loc x
        (let ([fn^ fn])
          (let ([arg^ arg] ...)
            (cond
             [valid-app? (#%app fn^ arg^ ...)]
             [else (raise-goal-as-fn-exn src)])))))]))

