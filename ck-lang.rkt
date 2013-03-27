#lang racket

(require "ck.rkt" (for-syntax "ck.rkt" racket/syntax))

(provide 
 (except-out (all-from-out racket) #%app)

 ;; mk things
 conde conda condu fresh succeed fail 
 run run* prt prtm use-constraints trace-define
 (rename-out [#%app-safe #%app]))

;; This is a tracing macro, akin to trace-define in Chez Scheme.  Upon
;; entry to the goal, all arguments to the function will be projected
;; in the current substitution and printed out.
(define-syntax trace-define
  (syntax-rules ()
    ((_ (name a* ...) body)
     (trace-define-mk name (lambda (a* ...) body)))
    ((_ name (λ (a* ...) body))
     (define name
       (λ (a* ...)
         (fresh ()
           (project (a* ...)
             (begin
               (display (list 'name a* ...))
               (newline)
               succeed))
           body))))))

;; Should be able to think of importing constraint files as using
;; constraints, not as requiring files.  Abstractiiooonnnnn.
(define-syntax-rule (use-constraints file ...) (require file ...))

;; =============================================================================

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
    [(a) #`(or (not (goal? #,fn)) (a? a))]
    [(a* ...) #`(not (goal? #,fn))]))

(define-syntax (#%app-safe x)
  (syntax-case x () 
    [(_ fn arg ...)
     (with-syntax* ([(fn^ arg^ ...) 
                     (generate-temporaries #'(fn arg ...))]
                    [src (build-srcloc #'fn)]
                    [valid-app? (valid-app?-pred #'fn^ #'(arg^ ...))])
       #'(let ((fn^ fn))
           (let ((arg^ arg) ...)
             (cond
              [valid-app? (#%app fn^ arg^ ...)]
              [else (raise-goal-as-fn-exn src)]))))]))

