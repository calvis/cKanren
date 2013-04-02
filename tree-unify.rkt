#lang racket

(require "ck.rkt")
(provide == unify)

;; ---UNIFICATION--------------------------------------------------

(define (unifiable-structs? u v)
  (and (mk-struct? u)
       (mk-struct? v)
       (unifiable? u v)
       (unifiable? v u)))

(define (unify e s)
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
         ((unifiable-structs? u v)
          (recur u 
           (lambda (ua ud)
             (recur v
              (lambda (va vd)
                (loop ua va `((,ud . ,vd) . ,e)))))))
         ((equal? u v) (unify e s))
         (else #f)))))))

;; ---GOAL---------------------------------------------------------

(define (== u v) (goal-construct (==-c u v)))

(define (==-c u v)
  (lambdam@ (a : s c)
    (cond
     ((unify `((,u . ,v)) s)
      => (lambda (s^)
           ((update-prefix s s^) a)))
     (else #f))))

(define (update-prefix s s^)
  (let loop ((s^ s^))
    (cond
     ((eq? s s^) identitym)
     (else
      (composem
       (update-s (caar s^) (cdar s^))
       (loop (cdr s^)))))))

