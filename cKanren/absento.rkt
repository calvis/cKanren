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
         ((symbol-uw? u (get-attributes u c))
          ((update-c (build-attr-oc symbol-c u symbol-uw?)) a))
         (else #f))))))
 
(define (symbol-uw? x attrs)
  (define incompatible '(number-c))
  (and (not (pair? x)) 
       (not (number? x))
       (or (not attrs)
           (andmap (lambda (aoc) 
                     (not (memq (attr-oc-type aoc) incompatible)))
                   attrs))))

(define symbol-constrained?
  (lambda (v c)
    (cond
     [(get-attributes v c)
      => (lambda (attrs) (findf symbol-attr? attrs))]
     [else #f])))

(define (symbol-attr? oc)
  (eq? (attr-oc-type oc) 'symbol-c))
 
(define reify-symbol-cs
  (default-reify-attr 'sym 'symbol-c
    (lambda (x* r) (remove-duplicates x*))))

;; numbero

(define numbero
  (lambda (u)
    (goal-construct (number-c u))))

(define (number-uw? x attrs)
  (define incompatible '(symbol-c))
  (and (not (pair? x)) 
       (not (symbol? x))
       (or (not attrs) 
           (andmap (lambda (aoc) 
                     (not (memq (oc-rator aoc) incompatible)))
                   attrs))))

(define number-c
  (lambda (u)
    (lambdam@ (a : s c)
      (let ((u (walk u s)))
        (cond
         ((number? u) a)
         ((not (var? u)) #f)
         ((number-uw? u (get-attributes u c))
          ((update-c (build-attr-oc number-c u number-uw?)) a))
         (else #f))))))

(define number-constrained?
  (lambda (v c)
    (cond
     [(get-attributes v c)
      => (lambda (attrs) (findf number-attr? attrs))]
     [else #f])))
 
(define remove-duplicates
  (lambda (l)
    (for/fold ([s '()])
              ([x l])
      (if (member x s) s (cons x s)))))

(define (number-attr? oc)
  (eq? (attr-oc-type oc) 'number-c))

(define reify-number-cs
  (default-reify-attr 'num 'number-c
    (lambda (x* r) (remove-duplicates x*))))

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
         ((mem-check u v a) #f)
         ((mem-check v u a) a)
         (else ((normalize-store (cons u v)) a)))))))

(define (normalize-store p)
  (lambdam@ (a : s c-old)
    (let ([acs (filter/rator 'absent-c c-old)])
      (let loop ([acs acs] [acs^ '()])
        (cond
         [(null? acs) 
          (let ([oc (build-oc absent-c (car p) (cdr p))])
            (bindm a 
              (composem 
               (replace-ocs 'absent-c acs^)
               (update-c oc))))]
         [else
          (let ([u (car (oc-rands (car acs)))]
                [v (cadr (oc-rands (car acs)))])
            (cond
             [(subsumes? p (cons u v) a)
              (loop (cdr acs) acs^)]
             [(subsumes? (cons u v) p a) a]
             [else (loop (cdr acs) (cons (car acs) acs^))]))])))))

(define (subsumes? p p^ a)
  (and (mem-check (car p) (car p^) a)
       (mem-check (cdr p) (cdr p^) a)))

(define mem-check
  (lambda (u t a)
    (or ((term= u t) a)
        (and (pair? t)
             (or (mem-check u (car t) a)
                 (mem-check u (cdr t) a))))))
 
(define term=
  (lambda (u t)
    (lambdam@ (a : s c)
      (cond
       ((unify `((,u . ,t)) s c) =>
        (lambda (s/c) (eq? (car s/c) s)))
       (else #f)))))

(define reify-absent-cs
  (default-reify 'absento '(absent-c) 
    (lambda (rands r)
      (remove-duplicates rands))))

(define (absento-split u v)
  (composem
   (absent-c u (car v))
   (absent-c u (cdr v))
   (=/=-c u v)))

(define type-cs '(number-c symbol-c))
(define (rerun-type-cs x)
  (fresh ()
    (elim-diseqs)
    (lambdag@ (a : s c)
      (let ([ocs (filter (lambda (oc) (memq (attr-oc-type oc) type-cs))
                         (filter/rator attr-tag c))])
        ((run-relevant-constraints (map (compose car oc-rands) ocs) c) a)))))

(define (elim-diseqs)
  (lambdag@ (a : s c)
    (let ([neqs (filter/rator '=/=neq-c c)]
          [absentos (filter/rator 'absent-c c)])
      (let ([neqs^ (map (lambda (oc) (filter-subsumed-prefixes oc absentos a)) neqs)])
        (let ([neqs^ (filter-not (compose null? oc-prefix) neqs^)])
          ((replace-ocs '=/=neq-c neqs^) a))))))

(define (filter-subsumed-prefixes oc absentos a)
  (define absento-pairs (map oc-rands absentos))
  (let ([p (oc-prefix oc)])
    (let ([p^
           (filter-not
            (lambda (u/v) ;; can I find u/v subsumed by abesntos
              (findf
               (lambda (abs)
                 (cond
                  [((term= abs u/v) a)]
                  [((term= abs (list (cdr u/v) (car u/v))) a)]
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


