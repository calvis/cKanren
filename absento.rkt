#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "tree-unify.rkt" "neq.rkt")
(provide symbolo numbero absento mem-check term=)

;; symbolo

(define symbolo
  (lambda (u)
    (goal-construct (symbol-c u))))

(define symbol-c
  (lambda (u)
    (lambdam@ (a : s c)
      (let ((u (walk u s)))
        (cond
         ((symbol? u) a)
         ((not (var? u)) #f)
         (else ((update-c (build-attr-oc symbol-c u symbol-uw?)) a)))))))
 
(define (symbol-uw? x attrs)
  (define incompatible '(number-c))
  (and (not (pair? x)) (not (number? x))
       (or (not attrs) (andmap (lambda (aoc) (not (memq (oc-rator aoc) incompatible)))
                               attrs))))

(define symbol-constrained?
  (lambda (v c)
    (findf (lambda (oc) (and (eq? (oc-rator oc) 'symbol-c) 
                             (eq? (car (oc-rands oc)) v))) c)))
 
(define reify-symbol-cs
  (default-reify 'sym '(symbol-c)
    (lambda (rands) (remove-duplicates (map car rands)))))

;; numbero

(define numbero
  (lambda (u)
    (goal-construct (number-c u))))

(define (number-uw? x attrs)
  (define incompatible '(symbol-c))
  (and (not (pair? x)) 
       (not (symbol? x))
       (or (not attrs) (andmap (lambda (aoc) (not (memq (oc-rator aoc) incompatible)))
                               attrs))))

(define number-c
  (lambda (u)
    (lambdam@ (a : s c)
      (let ((u (walk u s)))
        (cond
         ((number? u) a)
         ((not (var? u)) #f)
         (else ((update-c (build-attr-oc number-c u number-uw?)) a)))))))

(define number-constrained?
  (lambda (v c)
    (findf (lambda (oc) (and (eq? (oc-rator oc) 'number-c) 
                             (eq? (car (oc-rands oc)) v))) c)))
 
(define remove-duplicates
  (lambda (l)
    (for/fold ([s '()])
              ([x l])
      (if (member x s) s (cons x s)))))

(define reify-number-cs
  (default-reify 'num '(number-c) 
    (lambda (rands) (remove-duplicates (map car rands)))))

;; absento

(define absento
  (lambda (u v)
    (goal-construct (absent-c u v))))

(define absent-c
  (lambda (u v)
    (lambdam@ (a : s c)
      (let ([u (walk* u s)]
            [v (walk* v s)])
        (cond
         ((or (symbol? v) 
              (number? v)
              (symbol-constrained? v c)
              (number-constrained? v c))
          (cond
           [(pair? u) a]
           [else ((=/=-c u v) a)]))
         ((pair? v) ((absento-split u v) a))
         ((not (var? v)) ((=/=-c u v) a))
         ((mem-check u v s c) #f)
         ((mem-check v u s c) a)
         (else ((normalize-store (cons u v)) a)))))))

(define (normalize-store p)
  (lambdam@ (a : s c-old)
    (let loop ([c c-old] [c^ '()])
      (cond
       [(null? c) 
        (make-a s (ext-c (build-oc absent-c (car p) (cdr p)) c^))]
       [(eq? (oc-rator (car c)) 'absent-c)
        (let ([u (car (oc-rands (car c)))]
              [v (cadr (oc-rands (car c)))])
          (cond
           [(subsumes? p (cons u v) s c)
            (loop (cdr c) c^)]
           [(subsumes? (cons u v) p s c) a]
           [else (loop (cdr c) (cons (car c) c^))]))]
       [else (loop (cdr c) (cons (car c) c^))]))))

(define (subsumes? p p^ s c)
  (and (mem-check (car p) (car p^) s c)
       (mem-check (cdr p) (cdr p^) s c)))

(define mem-check
  (lambda (u t s c)
    (or (term= u t s c)
        (and (pair? t)
             (or (mem-check u (car t) s c)
                 (mem-check u (cdr t) s c))))))
 
(define term=
  (lambda (u t s c)
    (cond
     ((unify `((,u . ,t)) s c) =>
      (lambda (s^) (eq? s s^)))
     (else #f))))

(define reify-absent-cs
  (default-reify 'absento '(absent-c) remove-duplicates))

(define (absento-split u v)
  (composem
   (absent-c u (car v))
   (composem
    (absent-c u (cdr v))
    (=/=-c u v))))

(define type-cs '(number-c symbol-c))
(define (rerun-type-cs x)
  (fresh ()
    (elim-diseqs)
    (lambdag@ (a : s c)
      (let ([c^ (filter (lambda (oc) (memq (oc-rator oc) type-cs)) c)])
        ((run-constraints (map (compose car oc-rands) c^) c)
         a)))))

(define (elim-diseqs)
  (lambdag@ (a : s c)
    (let ([neqs (filter/rator '=/=neq-c c)]
          [absentos (filter/rator 'absent-c c)]
          [rest (filter-not/rator '=/=neq-c c)])
      (let ([neqs^ (map (lambda (oc) (filter-subsumed-prefixes oc absentos s c)) neqs)])
        (let ([neqs^ (filter-not (compose null? oc-prefix) neqs^)])
          (make-a s (append rest neqs^)))))))

(define (filter-subsumed-prefixes oc absentos s c)
  (define absento-pairs (map oc-rands absentos))
  (let ([p (oc-prefix oc)])
    (let ([p^
           (filter-not
            (lambda (u/v) ;; can I find u/v subsumed by abesntos
              (findf
               (lambda (abs)
                 (cond
                  [(term= abs u/v s c)]
                  [(term= abs (list (cdr u/v) (car u/v)) s c)]
                  [else #f]))
               absento-pairs))
            p)])
      (build-oc =/=neq-c p^))))

;; etc

(define booleano
  (lambda (x)
    (conde
      ((== #f x) succeed)
      ((== #t x) succeed))))
         
;; ckanren stuffs

(extend-enforce-fns 'absento rerun-type-cs)
(extend-reify-fns 'numbero reify-number-cs)
(extend-reify-fns 'symbolo reify-symbol-cs)
(extend-reify-fns 'absento reify-absent-cs)


