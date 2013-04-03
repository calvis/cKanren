#lang racket

(require "../ck.rkt")
(provide test (rename-out [test test-check]) test-divergence test-disable)

(define max-ticks 10000000)

(define-syntax (test x)
  (syntax-case x ()
    ((_ title tested-expression expected-result)
     (quasisyntax/loc x
      (begin
        (printf "Testing ~a\n" title)
        (let ([expected expected-result]
              [produced tested-expression])
          (cond
           [(equal? expected produced) (void)] 
           [else
            (make-error #,(build-srcloc x)
                        "error while running tests\nExpression: ~a~%Expected: ~a~%Computed: ~a~%"
                        'tested-expression expected produced)])))))))

(define (make-error src msg . exprs)
  (cond
   [(format-source src)
    => (lambda (loc) (apply error loc msg exprs))]
   [else (apply error 'test msg exprs)]))

(define-syntax test-divergence
  (syntax-rules ()
    ((_ title tested-expression)
     (begin
       (printf "Testing ~a (engine with ~s ticks fuel)\n" title max-ticks)
       (let ((eng (make-engine (lambda () tested-expression))))
         (eng max-ticks
           (lambda (t v)
             (error 'test-divergence
                    "infinite loop returned ~s after ~s ticks"
                    v (- max-ticks t)))
           (lambda (e^) (void))))))))

(define-syntax test-disable
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (printf "Disable testing ~s\n" title))))
