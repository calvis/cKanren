#lang racket

(require "../ck.rkt" "../tree-unify.rkt")

(define (appendo l s out)
  (goal-construct (append-c l s out)))

(define (append-c ls1 ls2 out)
  (lambdam@ (a : s c)
    ((update-c (build-oc append-c ls1 ls2 out)) a)))

(define (enforce-appendo oc)
  (let ([ls1 (car (oc-rands oc))]
        [ls2 (cadr (oc-rands oc))]
        [out (caddr (oc-rands oc))])
    (conde
     ((== ls1 '()) 
      (== ls2 out))
     ((fresh (a d res)
        (appendo d ls2 res)
        (== ls1 `(,a . , d))
        (== out `(,a . ,res)))))))

(define (do-enforce-appendo x)
  (lambdag@ (a : s c)
    ((let ([ocs (filter/rator 'append-c c)])
       (let loop ([ocs ocs])
         (cond
          [(null? ocs) succeed]
          [else 
           (fresh () 
             (enforce-appendo (car ocs))
             (loop (cdr ocs)))])))
     a)))

(define (append l s)
  (cond
   [(null? l) s]
   [else (cons (car l) (append (cdr l s)))]))


(extend-enforce-fns 'appendo do-enforce-appendo)
