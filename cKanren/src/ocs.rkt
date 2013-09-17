#lang racket

(require "helpers.rkt" "events.rkt" "variables.rkt" "mk-structs.rkt")
(require (for-syntax racket/syntax syntax/parse))

(provide (all-defined-out))

;; the representation of a constraint in the constraint store 
;; contains a closure waiting to be evaluated with a new package,
;; a symbolic representation of the constrant's name and it's args
(struct oc (proc rator rands subs reify)
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

(define (contains-relevant-var? vars e)
  (match e
    [(add-association-event x v)
     (or (memq x vars) 
         (and (var? v) (memq v vars)))]
    [(composite-event ls)
     (ormap (curry contains-relevant-var? vars) ls)]
    [_ #f]))

;; creates an oc given the constraint operation and it's args
(define-syntax (build-oc stx)
  (syntax-parse stx
    ((build-oc op:id reifyfn:expr arg:expr ...)
     (define/with-syntax (arg^ ...)
       (generate-temporaries #'(arg ...)))
     #'(let ([arg^ arg] ...)
         (define proc (op arg^ ...))
         (define rator 'op)
         (define rands (list arg^ ...))
         (make-oc 
          proc rator rands
          (curry contains-relevant-var? 
                 (filter*/var? rands))
          (reifyfn arg^ ...))))))


