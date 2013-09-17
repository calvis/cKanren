#lang racket/base

;; This file provides the minimum core of cKanren functionalities

(require "helpers.rkt")

(provide (except-out (all-defined-out) a))

;; the stream miniKanren runs on
;; (struct a-inf ())

;; the simple manifestations of the stream
;; (struct mzerof a-inf ())
;; (struct choiceg a-inf (a f))
;; (struct inc a-inf (e) 
;;   #:property prop:procedure (struct-field-index e)
;;   #:methods gen:custom-write 
;;   [(define (write-proc i port mode) 
;;      ((parse-mode mode) "#<inc>" port))])

(define mzerof (lambda () #f))
(define choiceg cons)

(struct a #;a-inf (s c q t e)
  #:extra-constructor-name make-a
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-package args))])

;; controls how packages are displayed
(define (write-package a port mode)
  (let ([fn (lambda (s) ((parse-mode mode) s port))])
    (if (debug?)
        (fn (format "#a{ ~s ~a ~a ~a }" (a-t a) (a-s a) (a-c a) (a-e a)))
        (fn (format "#a{ ~a ~a ~a }" (a-s a) (a-c a) (a-e a))))))

;; macro that delays expressions
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

;; delays an expression
(define-syntax delay
  (syntax-rules ()
    #;[(_ e) (inc (lambdaf@ () e))]
    [(_ e) (lambdaf@ () e)]
    ))

(define empty-f (delay (mzerof)))

;; convenience macro for dispatching on the type of a-inf
#;
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ([a-inf e])
       (cond
        [(mzerof? a-inf) e0]
        [(inc? a-inf) (let ([f^ (inc-e a-inf)]) e1)]
        [(a? a-inf) (let ([a^ a-inf]) e2)]
        [(choiceg? a-inf) (let ([a (choiceg-a a-inf)] [f (choiceg-f a-inf)]) e3)]
        [else (error 'case-inf "not an a-inf ~s" e)])))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ((a-inf e))
       (cond
        ((not a-inf) e0)
        ((procedure? a-inf)  (let ((f^ a-inf)) e1))
        ((not (and (pair? a-inf)
                   (procedure? (cdr a-inf))))
         (let ((a^ a-inf)) e2))
        (else (let ((a (car a-inf)) (f (cdr a-inf))) 
                e3)))))))



