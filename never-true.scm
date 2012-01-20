(library
  (never-true)
  (export never-trueo never-pairo requiredo allowedo)
  (import (rnrs) (ck))

(define never-true-c
  (lambda (pred? x)
    (lambdam@ (a : s c)
      (let ((x (walk x s)))
        (cond
          ((pred? x) #f)
          (else ((update-c (build-oc never-true-c pred? x)) a)))))))

(define never-trueo
  (lambda (pred? x)
    (goal-construct (never-true-c pred? x))))

(define never-pairo
  (lambda (x)
    (never-trueo pair? x)))

(define requiredo
  (lambda (pred? x)
    (goal-construct (required-c pred? x))))

(define required-c
  (lambda (pred? x)
    (lambdam@ (a : s c)
      (let ((x (walk* x s)))
        (cond
          ((pred? x) a)
          (else ((update-c (build-oc required-c pred? x)) a)))))))

(define required-enforce
  (lambda (x)
    (goal-construct (enforce-required))))

(define (enforce-required)
  (lambdam@ (a : s c)
    (and (not (find (lambda (oc) (eq? 'required-c (oc->rator oc))) c))
         a)))

(define allowedo
  (lambda (pred? x)
    (goal-construct (allowed-c pred? x))))

(define allowed-c
  (lambda (pred? x)
    (lambdam@ (a : s c)
      (let ((x (walk* x s)))
        (cond
          ((pred? x) a)
          (else ((update-c (build-oc allowed-c pred? x)) a)))))))

(define reified-allowed
  (lambda (v r c)
    (let ((c (filter (lambda (oc) (eq? (oc->rator oc) 'allowed-c)) c)))
      (let ((c (walk* (map cddr c) r)))
        `((allowed . ,c))))))

(extend-enforce-fns 'required required-enforce)
(extend-reify-fns 'allowed reified-allowed)

)

(import (never-true))
