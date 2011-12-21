(library
  (tree-unify)
  (export == unify)
  (import (rnrs) (ck))

;; ---UNIFICATION--------------------------------------------------

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or (occurs-check x (car v) s)
             (occurs-check x (cdr v) s)))
        (else #f)))))

(define unify
  (lambda (e s)
    (cond
      ((null? e) s)
      (else
       (let loop ((u (caar e)) (v (cdar e)) (e (cdr e)))
         (let ((u (walk u s)) (v (walk v s)))
           (cond
             ((eq? u v) (unify e s))
             ((var? u)
              (and (not (occurs-check u v s))
                   (unify e (ext-s u v s))))
             ((var? v)
              (and (not (occurs-check v u s))
                   (unify e (ext-s v u s))))
             ((and (pair? u) (pair? v))
              (loop (car u) (car v)
                `((,(cdr u) . ,(cdr v)) . ,e)))
             ((equal? u v) (unify e s))
             (else #f))))))))

;; ---GOAL---------------------------------------------------------

(define == (lambda (u v) (goal-construct (==-c u v))))

(define ==-c
  (lambda (u v)
    (lambdam@ (a : s c)
      (cond
        ((unify `((,u . ,v)) s)
         => (lambda (s^)
              ((update-prefix s s^) a)))
        (else #f)))))

(define update-prefix
  (lambda (s s^)
    (let loop ((s^ s^))
      (cond
        ((eq? s s^) identitym)
        (else
          (composem
            (update-s (caar s^) (cdar s^))
            (loop (cdr s^))))))))

)

(import (tree-unify))

