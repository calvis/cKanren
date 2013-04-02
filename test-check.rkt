#lang racket

(require "ck.rkt")
(provide test (rename-out [test test-check]) test-disable)

(define errorf error)

(define-syntax test
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (cond
           ((equal? expected produced))
           (else
             (errorf 'test
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced))))))))

(define-syntax test-disable
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Disable testing ~s\n" title)
       #t))))
