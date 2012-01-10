(library
  (never-true)
  (export never-true never-pairo)
  (import (rnrs) (ck))

(define never-true-c
  (lambda (pred? x)
    (lambdam@ (a : s c)
      (let ((x (walk x s)))
        (cond
          ((pred? x) #f)
          (else ((update-c (build-oc never-true-c pred? x)) a)))))))

(define never-true
  (lambda (pred? x)
    (goal-construct (never-true-c pred? x))))

(define never-pairo
  (lambda (x)
    (never-true pair? x)))

)

(import (never-true))
