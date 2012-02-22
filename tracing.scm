(library (tracing)
  (export trace-define-mk)
  (import
    (rnrs)
    (mk)
    (only (chezscheme) printf))

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
               (printf "~s\n" (list 'name a* ...))
               succeed))
           body))))))

)