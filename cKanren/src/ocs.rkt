#lang racket

(require "helpers.rkt")

(provide (all-defined-out))

;; the representation of a constraint in the constraint store 
;; contains a closure waiting to be evaluated with a new package,
;; a symbolic representation of the constrant's name and it's args
(struct oc (proc rator rands) 
  #:extra-constructor-name make-oc
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-oc args))])

;; displays an oc
(define (write-oc oc port mode)
  (define fn (lambda (str) ((parse-mode mode) str port)))
  (fn (format "#oc<~a" (oc-rator oc)))
  (for ([arg (oc-rands oc)])
    (fn (format " ~a" arg)))
  (fn (format ">")))

;; creates an oc given the constraint operation and it's args
(define-syntax (build-oc x)
  (syntax-case x ()
    ((_ op arg ...)
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       #'(let ((arg^ arg) ...)
           (make-oc (op arg^ ...) 'op `(,arg^ ...)))))))

