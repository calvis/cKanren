(library
  (neq)
  (export =/= add=/=)
  (import (rnrs) (mk) (ck) (only (tree-unify) unify)
    (only (chezscheme) pretty-print trace-define))

;;; little helpers

(define recover/vars
  (lambda (p)
    (cond
      ((null? p) '())
      (else
        (let ((x (lhs (car p)))
              (v (rhs (car p)))
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

(define oc->prefix
  (lambda (oc)
    (car (oc->rands oc))))

(define reify-constraintsneq
  (lambda (v r)
    (lambdag@ (a : s c)
      (let ((c (filter (lambda (oc) (eq? (oc->rator oc) '=/=neq-c)) c)))
        (let ((c (remp any/var? (walk* (map oc->prefix c) r))))
          (cond
            ((null? c) '())
            (else `((=/= . ,(walk* c r))))))))))

(define =/=neq-c
  (lambda (p)
    (lambdam@ (a : s c)
      (cond
        ((unify p s)
         =>
         (lambda (s^)
           (let ((p (prefix-s s s^)))
             (cond
               ((null? p) #f)
               (else ((normalize-store p) a))))))
        (else a)))))

(define normalize-store
  (lambda (p)
    (lambdam@ (a : s c)
      (let loop ((c c) (c^ '()))
        (cond
          ((null? c)
           (let ((c^ (ext-c (build-oc =/=neq-c p) c^)))
             (make-a s c^)))
          ((eq? (oc->rator (car c)) '=/=neq-c)
           (let* ((oc (car c))
                  (p^ (oc->prefix oc)))
             (cond
               ((subsumes? p^ p) a)
               ((subsumes? p p^) (loop (cdr c) c^))
               (else (loop (cdr c) (cons oc c^))))))
          (else (loop (cdr c) (cons (car c) c^))))))))

(define subsumes?
  (lambda (p s)
    (cond
      ((unify p s) => (lambda (s^) (eq? s s^)))
      (else #f))))

;;; goals

(define =/=
  (lambda (u v)
    (goal-construct (=/=-c u v))))

(define =/=-c
  (lambda (u v)
    (lambdam@ (a : s c)
      (cond
        ((unify `((,u . ,v)) s)
         => (lambda (s^)
              ((=/=neq-c (prefix-s s s^)) a)))
        (else a)))))

(define add=/=
  (lambda ()
    (extend-reify-fns reify-constraintsneq)))

)

(import (neq))
(add=/=)
