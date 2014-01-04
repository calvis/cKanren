#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "tree-unify.rkt" (only-in "neq.rkt" =/= !=/prefix) 
         "src/helpers.rkt" "attributes.rkt"
         "src/framework.rkt" "src/events.rkt" "src/constraints.rkt")
(provide absento mem-check term=)

;; absento

(define (symbol-constrained? v attrs)
  (ormap (curry eq? symbol) attrs))
(define (number-constrained? v attrs)
  (ormap (curry eq? number) attrs))

(define-constraint (absento [u walk*] v)
  #:reified
  #:package (a [s c e])
  #:reaction
  [(unify-change (list (cons u v)))
   ;; (printf "absento: u: ~a v: ~a\n" u v)
   (cond
    [(or (symbol? v) 
         (number? v)
         (cond
          [(get-attributes v c e)
           => (lambda (attrs)
                (or (symbol-constrained? v attrs)
                    (number-constrained? v attrs)))]
          [else #f]))
     (cond
      [(pair? u) succeed]
      [else (=/= u v)])]
    [(pair? v) (absento-split u v)]
    [(not (var? v)) (=/= u v)]
    [(eq? u v) fail]
    [(mem-check v u s c e) succeed]
    [else (add-constraint (absento u v))])])

(define-constraint-interaction
  [(absento u v) (absento u^ v^)]
  #:package [a [s c e]]
  [(subsumes? (cons u v) (cons u^ v^) s c e)
   [(absento u v)]])

(define (subsumes? p p^ s c e)
  (and (mem-check (car p) (car p^) s c e)
       (mem-check (cdr p) (cdr p^) s c e)))

(define mem-check
  (lambda (u t s c e)
    (or (term= u t s c e)
        (and (pair? t)
             (or (mem-check u (car t) s c e)
                 (mem-check u (cdr t) s c e))))))
 
(define term=
  (lambda (u t s c e)
    (cond
     [(unify `((,u . ,t)) s c e) =>
      (lambda (s/c) (eq? (car s/c) s))]
     [else #f])))

(define (absento-split u v)
  (conj
   (absento u (car v))
   (absento u (cdr v))
   (=/= u v)))

(define-constraint-interaction
  [(!=/prefix prefix) (absento u v)]
  #:package (a [s c e])
  [(ormap
    (lambda (u/v)
      (or (term= (cons u v) u/v s c e)
          (term= (cons v u) u/v s c e)))
    prefix)
   [(let ([p^ (filter-not
               (lambda (u/v) ;; can I find u/v subsumed by abesntos
                 (or (term= (cons u v) u/v s c e)
                     (term= (cons v u) u/v s c e))) ;; TODO dumb
               prefix)])
      (conj 
       (cond
        [(null? p^) succeed]
        [else (!=/prefix p^)])
       (absento u v)))]])

