#lang racket

(require "ck.rkt" (only-in "tree-unify.rkt" unify))
(provide =/= =/=neq-c oc-prefix reify-prefix-dot
         (rename-out [=/= !=]))

;;; little helpers

(define (recover/vars p)
  (cond
   [(null? p) '()]
   [else
    (let ([x (car (car p))]
          [v (cdr (car p))]
          [r (recover/vars (cdr p))])
      (cond
       [(var? v) (ext/vars v (ext/vars x r))]
       [else (ext/vars x r)]))]))

(define (ext/vars x r)
  (cond
   ((memq x r) r)
   (else (cons x r))))

;;; serious functions

(define (oc-prefix oc)
  (car (oc-rands oc)))

(define reify-prefix-dot 
  (make-parameter #t))

(define (remove-dots p)
  (cond
   [(reify-prefix-dot) p]
   [else (list (car p) (cdr p))]))

(define (sort-p p)
  (sort-by-lex<=
   (map (lambda (a) (sort-diseq (car a) (cdr a))) p)))

(define (sort-diseq u v)
  (cond
   ((char<?
     (string-ref (format "~s" v) 0)
     (string-ref "_" 0))
    (cons u v))
   ((lex<= u v) (cons u v))
   (else (cons v u))))

(define-constraint (=/=neq-c [p walk*])
  #:package (a [s c e])
  #:reification-function
  (lambda (v r)
    (values '=/= (remove-dots (sort-p p))))
  (cond
   [(unify p s c)
    =>
    (lambda (s/c)
      (define p (prefix-s s (car s/c)))
      (cond
       [(null? p) fail]
       [else (update-c (=/=neq-c p))]))]
   [else succeed]))

;; how to read this: 
;; neq-subsume defines an interaction between =/=neq-c constraints
;; if there are two =/=neq-c constraints with prefixes p and p^
;; in the constraint store, if the first subsumes the second, keep
;; only the first constraint.  this is reflexive by default.
(define-constraint-interaction neq-subsume
  ((=/=neq-c ,p) (=/=neq-c ,p^))
  #:package (a [s c e])
  [(subsumes? p p^ c) ((=/=neq-c p))])

(define (subsumes? p p^ c)
  (cond
   [(unify p p^ c) => 
    (lambda (s/c) (eq? (car s/c) p^))]
   [else #f]))

;;; goals

(define (=/= u v)
  (constraint
   #:package (a [s c e])
   (cond
    [(unify `((,u . ,v)) s c)
     => (lambda (s/c)
          (=/=neq-c (prefix-s s (car s/c))))]
    [else succeed])))


