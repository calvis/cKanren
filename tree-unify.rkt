#lang racket

(require "ck.rkt")
(provide == ==-c unify)

;; ---UNIFICATION--------------------------------------------------

(define (unifiable-structs? u v)
  (and (mk-struct? u)
       (mk-struct? v)
       (unifiable? u v)
       (unifiable? v u)))

;; returns #t if attributes are ok
(define (check-attributes u v c)
  (let ([ua (get-attributes u c)]
        [va (get-attributes v c)])
    (cond
     [(and (not ua) (not va)) #t]
     [else
      (and (or (not ua) (andmap (lambda (aoc) ((attr-oc-uw? aoc) v va)) ua))
           (or (not va) (andmap (lambda (aoc) ((attr-oc-uw? aoc) u ua)) va)))])))

(define (unify e s c)
  (cond
   ((null? e) s)
   (else
    (let loop ((u (caar e)) (v (cdar e)) (e (cdr e)))
      (let ((u (walk u s)) (v (walk v s)))
        (cond
         ((eq? u v) (unify e s c))
         ((and (or (var? u) (var? v))
               (not (check-attributes u v c)))
          #f)
         ((var? u)
          (and (not (occurs-check u v s))
               (unify e (ext-s u v s) c)))
         ((var? v)
          (and (not (occurs-check v u s))
               (unify e (ext-s v u s) c)))
         ((unifiable-structs? u v)
          (recur u 
           (lambda (ua ud)
             (recur v
              (lambda (va vd)
                (loop ua va `((,ud . ,vd) . ,e)))))))
         ((equal? u v) (unify e s c))
         (else #f)))))))

;; ---GOAL---------------------------------------------------------

(define (== u v) (goal-construct (==-c u v)))

(define (==-c u v)
  (lambdam@ (a : s c)
    (cond
     ((unify `((,u . ,v)) s c)
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

