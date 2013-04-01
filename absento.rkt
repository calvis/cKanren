#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "tree-unify.rkt" "neq.rkt")
(provide symbolo numbero absento)

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
         (else ((update-c (build-oc symbol-c u)) a)))))))
 
(define symbol-constrained?
  (lambda (v c)
    (findf (lambda (oc) (and (eq? (oc->rator oc) 'symbol-c) 
                             (eq? (car (oc->rands oc)) v))) c)))
 
(define (reify-symbol-cs v r c)
  (let ([c (filter (lambda (oc) (eq? (oc->rator oc) 'symbol-c)) c)])
    (let ([ocs (map (lambda (oc) (walk (car (oc->rands oc)) r)) c)])
      (let ([ocs (filter-not any/var? ocs)])
        (cond
         [(null? ocs) '()]
         [else `((sym . ,(remove-duplicates ocs)))])))))

;; numbero

(define numbero
  (lambda (u)
    (goal-construct (number-c u))))

(define number-c
  (lambda (u)
    (lambdam@ (a : s c)
      (let ((u (walk u s)))
        (cond
         ((number? u) a)
         ((not (var? u)) #f)
         (else ((update-c (build-oc number-c u)) a)))))))

(define number-constrained?
  (lambda (v c)
    (findf (lambda (oc) (and (eq? (oc->rator oc) 'number-c) 
                             (eq? (car (oc->rands oc)) v))) c)))
 
(define (reify-number-cs v r c)
  (let ([c (filter (lambda (oc) (eq? (oc->rator oc) 'number-c)) c)])
    (let ([ocs (map (lambda (oc) (walk (car (oc->rands oc)) r)) c)])
      (let ([ocs (filter-not any/var? ocs)])
        (cond
         [(null? ocs) '()]
         [else `((num . ,(remove-duplicates ocs)))])))))

;; absento

(define absento
  (lambda (u v)
    (goal-construct (absent-c u v))))

(define absent-c
  (lambda (u v)
    (lambdam@ (a : s c)
      (let ([u (walk u s)]
            [v (walk v s)])
        (cond
         ((mem-check u v s) #f)
         ((or (symbol? v) (symbol-constrained? v c)
              (number? v) (number-constrained? v c))
          ((=/=-c u v) a))
         ((pair? v) ((absento-split u v) a))
         ((not (var? v)) ((=/=-c u v) a))
         (else ((update-c (build-oc absent-c u v)) a)))))))

(define mem-check
  (lambda (u t s)
    (or (term=? u t s)
        (and (pair? t)
             (mem-check u (car t) s)
             (mem-check u (cdr t) s)))))
 
(define term=?
  (lambda (u t s)
    (cond
     ((unify `((,u . ,t)) s) =>
      (lambda (s0) (eq? s0 s)))
     (else #f))))

(define (reify-absent-cs v r c)
  (let ([c (filter (lambda (oc) (eq? (oc->rator oc) 'absent-c)) c)])
    (let ([ocs (map (lambda (oc) (walk* (oc->rands oc) r)) c)])
      (let ([ocs (filter-not any/var? ocs)])
        (cond
         [(null? ocs) '()]
         [else `((absento . ,(remove-duplicates ocs)))])))))

(define (absento-split u v)
  (lambdam@ (a : s c)
    ((composem
      (absent-c u (car v))
      (composem
       (absent-c u (cdr v))
       (=/=-c u v)))
     a)))

;; etc

(define booleano
  (lambda (x)
    (conde
      ((== #f x) succeed)
      ((== #t x) succeed))))
         
(define remove-duplicates
  (lambda (l)
    (for/fold ([s '()])
              ([x l])
      (if (member x s) s (cons x s)))))

;; ckanren stuffs

(extend-reify-fns 'numbero reify-number-cs)
(extend-reify-fns 'symbolo reify-symbol-cs)
(extend-reify-fns 'absento reify-absent-cs)


