#lang racket

(require "ck.rkt" (only-in "tree-unify.rkt" unify unify-change) "src/events.rkt"
         "src/framework.rkt")
(provide =/= !=/prefix reify-prefix-dot (rename-out [=/= !=]) subsumes?)

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

(define-constraint (!=/prefix p)
  #:package (a [s c e])
  #:reaction
  [(unify-change p)
   =>
   (match-lambda
     [(cons new-p c)
      ;; (printf "\n!=/prefix: ~a ~a ~a\n" new-p c e)
      (cond
       [(null? new-p) fail]
       [else (add-constraint (!=/prefix new-p))])]
     [#f succeed])]
  #:reification-function
  (lambda (v r) (reified-constraint '=/= (sort-p p) r)))

;; how to read this: 
;; neq-subsume defines an interaction between !=/prefix constraints
;; if there are two !=/prefix constraints with prefixes p and p^
;; in the constraint store, if the first subsumes the second, keep
;; only the first constraint.  this is reflexive by default.
(define-constraint-interaction neq-subsume
  [(!=/prefix p) (!=/prefix p^)]
  #:package (a [s c e])
  [(subsumes? p p^ c) [(!=/prefix p)]])

(define (subsumes? p p^ c)
  (cond
   [(unify p p^ empty-c empty-e) => 
    (lambda (s/c) (eq? (car s/c) p^))]
   [else #f]))

;;; goals

(define (=/= u v)
  (transformer
   #:package (a [s c e])
   (cond
    [(unify `((,u . ,v)) s c e)
     => (lambda (s/c)
          (!=/prefix (prefix-s s (car s/c))))]
    [else succeed])))


