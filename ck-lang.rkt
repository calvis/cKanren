#lang racket

(require (rename-in "ck.rkt"
                    [run  run-unsafe]
                    [run* run*-unsafe]))
(provide (except-out (all-from-out racket) #%app)
         conde conda condu fresh succeed fail 
         run run* prt prtm use-constraints
         (rename-out
          [#%app-safe #%app]
          [trace-define-mk trace-define]))

(define-syntax-rule (run n (q) g g* ...)
  (parameterize ([safe-goals? #t])
    (take n (lambdaf@ ()
              ((fresh (q) g g* ...
                 (enforce-constraints q) 
                 (reify q))
               empty-a)))))

(define-syntax-rule (run* (q) g g* ...)
  (run #f (q) g g* ...))

(define-syntax trace-define-mk
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

(define-syntax-rule (use-constraints file ...)
  (require file ...))

(define-struct (exn:goal-as-fn exn:fail) ())

(define (raise-goal-as-fn-exn fn arg src)
  (raise
   (make-exn:goal-as-fn
    (format "goal ~s applied as a function at ~a:~s:~s" 
            fn
            (let ((p (srcloc-source src)))
              (if (path? p) (path->string p) p))
            (srcloc-line src)
            (srcloc-column src))
    (current-continuation-marks))))

(define-syntax (#%app-safe x)
  (syntax-case x () 
    [(_ fn arg)
     (quasisyntax/loc x
      (let ((arg^ arg))
        (let ((fn^ fn))
          (cond
           [(or (not (goal? fn^)) (a? arg^)) 
            (#%app fn^ arg^)]
           [else 
            (raise-goal-as-fn-exn 
             'fn
             '(arg)
             (srcloc '#,(syntax-source #'fn)
                     '#,(syntax-line #'fn)
                     '#,(syntax-column #'fn)
                     '#,(syntax-position #'fn)
                     '#,(syntax-span #'fn)))]))))]
    [(_ fn arg ...) 
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       (quasisyntax/loc 
        x
        (let ((arg^ arg) ...)
          (let ((fn^ fn))
            (cond
             [(not (goal? fn)) (#%app fn^ arg^ ...)]
             [else
              (raise-goal-as-fn-exn 
               'fn
               '(arg ...)
               (srcloc '#,(syntax-source #'fn)
                       '#,(syntax-line #'fn)
                       '#,(syntax-column #'fn)
                       '#,(syntax-position #'fn)
                       '#,(syntax-span #'fn)))])))))]))
