#lang racket

(require "variables.rkt" "helpers.rkt" "infs.rkt" "errors.rkt")
(require (for-syntax syntax/parse racket/syntax racket/match))

(provide (all-defined-out))

;; calling a constraint returns a structure that could be applied or
;; stored in the constraint store
(struct -constraint (fn reaction reifyfn add rem)
        #:property prop:procedure
        (lambda (this . args) 
          (oc this args)))

;; applying an oc acts like just calling the constraint on the
;; arguments; also has enough information to store in constraint store
(struct oc (rator rands)
        #:transparent
        #:methods gen:custom-write 
        [(define (write-proc this port mode)
           ((parse-mode mode) (format "#oc~a" (cons (oc-rator this) (oc-rands this))) port))]
        #:property prop:procedure
        (lambda (this a)
          (match-define (oc rator rands) this)
          (bindm a (apply (-constraint-fn rator) rands))))

;; a transformer takes a package and returns a package
(struct -transformer (fn)
        #:property prop:procedure (struct-field-index fn)
        #:methods gen:custom-write 
        [(define (write-proc this port mode)
           ((parse-mode mode) "#<transformer>" port))])
(define transformer? -transformer?)

;; splitting up the package
(define-syntax (lambda@ stx)
  (syntax-parse stx
    [(k (a:id) body:expr ...)
     (define/with-syntax src (build-srcloc-stx #'k))
     (syntax/loc stx 
       (let ()
         (define a-lambda@
           (case-lambda
            [(a) (let () body ...)]
            [r (raise
                (exn:goal-as-fn
                 (format "~s: misused lambda@" (format-source src))
                 (current-continuation-marks)))]))
         (-transformer a-lambda@)))]
    [(_ (a [s:id c:id q:id t:id e:id]) body:expr ...)
     (syntax/loc stx
       (lambda@ (a)
         (let ([s (a-s a)] 
               [c (a-c a)]
               [q (a-q a)]
               [t (a-t a)]
               [e (a-e a)])
           body ...)))]))

;; the failure value
(define mzerom (mzerof))

;; applies a goal to an a-inf and returns an a-inf
(define (bindm a-inf g)
  (case-inf a-inf
   [() (mzerof)]
   [(f) (delay (bindm (f) g))]
   [(a) (app-goal g a)]
   [(a f) (mplusm (app-goal g a) (delay (bindm (f) g)))]))

;; performs a conjunction over goals applied to an a-inf
(define-syntax (bindm* stx)
  (syntax-parse stx
    [(bindm* a-inf) 
     (syntax/loc stx a-inf)]
    [(bindm* a-inf g g* ...)
     (syntax/loc stx
       (bindm* (bindm a-inf g) g* ...))]))

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

(define-syntax (app-goal stx)
  (syntax-parse stx
    [(app-goal g a) (syntax/loc stx (g a))]))

(define (non-goal-error-msg val)
  (string-append
   "expression evaluated to non-ct where a ct was expected"
   (format "\n  value: ~s" val)))

(define (wrap-goal val src)
  (cond
   [(transformer? val) val]
   [(format-source src) => 
    (lambda (loc) (error loc (non-goal-error-msg val)))]
   [else (error (non-goal-error-msg val))]))

(define-syntax (start stx)
  (syntax-parse stx
    [(start a g g* ...)
     (syntax/loc stx (bindm* (app-goal g a) g* ...))]))

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
    [(a) #`(or (not (oc? #,fn)) (a? a))]
    [(a* ...) #`(not (oc? #,fn))]))

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

