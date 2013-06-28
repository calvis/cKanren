#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "tree-unify.rkt" "neq.rkt" "src/helpers.rkt" "attributes.rkt")
(provide absento mem-check term=)

;; absento

(define (absento u v)
  (lambdam@ (a : s c e)
    (let ([u (walk* u s)]
          [v (walk v s)])
      (cond
       [(or (symbol? v) 
            (number? v)
            (cond
             [(get-attributes v c)
              => (lambda (attrs)
                   (or (symbol-constrained? v attrs)
                       (number-constrained? v attrs)))]
             [else #f]))
        (cond
         [(pair? u) a]
         [else ((=/= u v) a)])]
       [(pair? v) ((absento-split u v) a)]
       [(not (var? v)) ((=/= u v) a)]
       [(eq? u v) mzerom]
       [(mem-check v u s c) a]
       [else ((normalize-store u v) a)]))))

(define (normalize-store u v)
  (lambdam@ (a : s c)
    (define acs (filter/rator 'absento c))
    (bindm a (remove-subsumed-absentos u v acs s c))))

(define (remove-subsumed-absentos u v acs s c)
  (define p (cons u v))
  (let remove-subsumed-absento-loop ([acs acs] [acs^ '()])
    (cond
     [(null? acs) 
      (define oc (build-oc absento u v))
      (define new-acs (cons oc acs^))
      (replace-ocs 'absento new-acs)]
     [else
      (define rands (oc-rands (car acs)))
      (define p^ (cons (car rands) (cadr rands)))
      (cond
       [(subsumes? p p^ s c)
        (remove-subsumed-absento-loop (cdr acs) acs^)]
       [(subsumes? p^ p s c)
        identitym]
       [else (remove-subsumed-absento-loop
              (cdr acs) (cons (car acs) acs^))])])))

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
     [(unify `((,u . ,t)) s c) =>
      (lambda (s/c) (eq? (car s/c) s))]
     [else #f])))

(define reify-absentos
  (default-reify 'absento '(absento) 
    (lambda (rands r)
      (remove-duplicates rands))))

(define (absento-split u v)
  (conj
   (absento u (car v))
   (absento u (cdr v))
   (=/= u v)))

(define (elim-diseqs x)
  (lambdam@ (a : s c)
    (let ([neqs (filter/rator '=/=neq-c c)]
          [absentos (filter/rator 'absento c)])
      (let ([neqs^ (map (lambda (oc) (filter-subsumed-prefixes oc absentos s c)) neqs)])
        (let ([neqs^ (filter-not (compose null? oc-prefix) neqs^)])
          (bindm a (replace-ocs '=/=neq-c neqs^)))))))

(define (filter-subsumed-prefixes oc absentos s c)
  (define absento-pairs (map oc-rands absentos))
  (let ([p (oc-prefix oc)])
    (let ([p^
           (filter-not
            (lambda (u/v) ;; can I find u/v subsumed by abesntos
              (findf
               (lambda (abs)
                 (or (term= abs u/v s c)
                     (term= abs (list (cdr u/v) (car u/v)) s c)))
               absento-pairs))
            p)])
      (build-oc =/=neq-c p^))))

;; ckanren stuffs

(extend-enforce-fns 'absento elim-diseqs)
(extend-reify-fns 'absento reify-absentos)


