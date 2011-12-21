(library
  (neq)
  (export =/=)
  (import (rnrs) (ck)
    (only (tree-unify) unify))

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
  (lambda (v r c)
    (let ((c (filter (lambda (oc) (eq? (oc->rator oc) '=/=neq-c)) c)))
      (let ((p* (walk* (map oc->prefix c) r)))
        (let ((p* (remp any/var? p*)))
          (cond
            ((null? p*) '())
            (else `((=/= . ,p*)))))))))

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

(extend-reify-fns 'neq reify-constraintsneq)

)

(import (neq))
