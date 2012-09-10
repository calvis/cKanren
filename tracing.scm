(library (cKanren tracing)
  (export trace-define-mk)
  (import (rnrs) (cKanren mk))

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

)