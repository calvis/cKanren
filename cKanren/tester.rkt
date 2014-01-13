#lang racket

(require "src/errors.rkt")
(provide test 
         (rename-out [test test-check])
         test-divergence
         test-disable
         test-any-order
         test-highlight)

(define max-ticks 10000000)

(define-syntax (test x)
  (define (test-syntax te er)
    (define new-te
      (quasisyntax/loc x
        (with-handlers 
         ([(lambda (x) #t)
           (lambda (e) 
             (cond
              [(format-source #,(build-srcloc-stx x))
               => (lambda (loc) (printf "encountered exception while running ~a\n" loc))])
             (raise e))])
         #,te)))
    (quasisyntax/loc x
      (let ([expected #,er] [produced #,new-te])
        (cond
         [(equal? expected produced) (void)] 
         [else
          (make-error #,(build-srcloc-stx x)
                      (string-append
                       "error while running tests\n"
                       "expression: ~a~%expected: ~a~%computed: ~a~%")
                      '#,te expected produced)]))))
  (syntax-case x ()
    ((_ title tested-expression expected-result)
     (quasisyntax/loc x
      (begin
        (printf "warning: depricated testing format in ~a\n" title)
        #,(test-syntax #'tested-expression #'expected-result))))
    ((_ tested-expression expected-result)
     (quasisyntax/loc x
       #,(test-syntax #'tested-expression #'expected-result)))))

(define-syntax (test-highlight x)
  (syntax-case x ()
    [(k stuff ...)
     (syntax/loc x
       (begin (printf (make-string 80 #\=))
              (newline)
              (test stuff ...)
              (printf (make-string 80 #\=))
              (newline)))]))

(define (make-error src msg . exprs)
  (cond
   [(format-source src)
    => (lambda (loc) (apply error loc msg exprs))]
   [else (apply error 'test msg exprs)]))

(define-syntax test-divergence
  (syntax-rules ()
    ((_ title tested-expression)
     (begin
       (printf "testing ~a (engine with ~s ticks fuel)\n" title max-ticks)
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
     (printf "disable testing ~s\n" title))))

(define-syntax (test-any-order x)
  (define (test-syntax te er)
    (quasisyntax/loc x
      (let ([expected #,er] [produced #,te])
        (cond
         [(and (= (length expected)
                  (length produced))
               (for/and 
                ([e expected])
                (member e produced)))
          (void)]
         [else
          (make-error #,(build-srcloc-stx x)
                      (string-append
                       "error while running tests\n"
                       "expression: ~a~%expected: ~a~%computed: ~a~%")
                      '#,te expected produced)]))))
  (syntax-case x ()
    ((_ title tested-expression expected-result)
     (quasisyntax/loc x
       (begin
         (printf "testing ~a\n" title)
         #,(test-syntax #'tested-expression #'expected-result))))
    ((_ tested-expression expected-result)
     (quasisyntax/loc x
       #,(test-syntax #'tested-expression #'expected-result)))))
