#lang racket

(require "ck.rkt" (only-in "tree-unify.rkt" unify))
(provide =/= =/=-c =/=neq-c oc-prefix reify-prefix-dot)

;;; little helpers

(define recover/vars
  (lambda (p)
    (cond
      ((null? p) '())
      (else
        (let ((x (car (car p)))
              (v (cdr (car p)))
              (r (recover/vars (cdr p))))
          (cond
            ((var? v) (ext/vars v (ext/vars x r)))
            (else (ext/vars x r))))))))

(define ext/vars
  (lambda (x r)
    (cond
      ((memq x r) r)
      (else (cons x r)))))

;;; serious functions

(define oc-prefix
  (lambda (oc)
    (car (oc-rands oc))))

(define reify-prefix-dot (make-parameter #t))

(define reify-constraintsneq
  (lambda (v r c)
    (let ((c (filter (lambda (oc) (eq? (oc-rator oc) '=/=neq-c)) c)))
      (let ((p* (walk* (map oc-prefix c) r)))
        (let ((p* (sort-p* (filter-not any/var? p*))))
          (cond
            ((null? p*) '())
            ((reify-prefix-dot) `((=/= . ,p*)))
            (else `((=/= . ,(map remove-dots p*))))))))))

(define (remove-dots p*)
  (map (lambda (p) (list (car p) (cdr p))) p*))

(define (sort-p* p*)
  (sort-by-lex<=
   (map (lambda (p)
          (sort-by-lex<=
           (map (lambda (a)
                 (let ([u (car a)] [v (cdr a)])
                   (sort-diseq u v)))
               p)))
        p*)))

(define (sort-diseq u v)
  (cond
  ((char<?
      (string-ref (format "~s" v) 0)
      (string-ref "_" 0))
   (cons u v))
  ((lex<= u v) (cons u v))
  (else (cons v u))))

(define =/=neq-c
  (lambda (p)
    (lambdam@ (a : s c)
      (let ([p (walk* p s)])
        (cond
         ((unify p s c)
          =>
          (lambda (s^)
            (let ((p (prefix-s s s^)))
              (cond
               ((null? p) #f)
               (else ((normalize-store p) a))))))
         (else a))))))

(define normalize-store
  (lambda (p)
    (lambdam@ (a : s c-old)
      (let loop ((c c-old) (c^ '()))
        (cond
          ((null? c)
           (let ((c^ (ext-c (build-oc =/=neq-c p) c^)))
             (make-a s c^)))
          ((eq? (oc-rator (car c)) '=/=neq-c)
           (let* ((oc (car c))
                  (p^ (oc-prefix oc)))
             (cond
               ((subsumes? p^ p c-old) a)
               ((subsumes? p p^ c-old) (loop (cdr c) c^))
               (else (loop (cdr c) (cons oc c^))))))
          (else (loop (cdr c) (cons (car c) c^))))))))

(define subsumes?
  (lambda (p s c)
    (cond
      ((unify p s c) => (lambda (s^) (eq? s s^)))
      (else #f))))

;;; goals

(define =/=
  (lambda (u v)
    (goal-construct (=/=-c u v))))

(define =/=-c
  (lambda (u v)
    (lambdam@ (a : s c)
      (cond
        ((unify `((,u . ,v)) s c)
         => (lambda (s^)
              ((=/=neq-c (prefix-s s s^)) a)))
        (else a)))))

(extend-reify-fns 'neq reify-constraintsneq)

