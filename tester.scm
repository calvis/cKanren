(library
  (tester)
  (export test-check test-divergence)
  (import (rnrs) (compat))

(define test-error
  (lambda (tag . args)
    (printf "Failed: ~s: ~%" tag)
    (apply printf args)
    (error 'WiljaCodeTester "That's all, folks!")))

(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~a\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (test-error 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))

(define max-ticks 10000000)

(define-syntax test-divergence
  (syntax-rules ()
    ((_ title tested-expression)
     (begin
       (printf "Testing ~s (engine with ~s ticks fuel)\n" title max-ticks)
       (let ((eng (make-engine (lambda () tested-expression))))
         (eng max-ticks
           (lambda (t v)
             (test-error 'test-divergence
               "infinite loop returned ~s after ~s ticks"
               v (- max-ticks t)))
           (lambda (e^) (void))))))))

)

(import (tester))

