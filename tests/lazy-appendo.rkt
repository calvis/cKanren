#lang racket

(require "../ck.rkt" "../tree-unify.rkt")

(define (appendo l s out)
  (goal-construct (append-c l s out)))

(define (append-c ls1 ls2 out)
  (lambdam@ (a : s c)
    ((update-c (build-oc append-c ls1 ls2 out)) a)))

(define (enforce-appendo oc)
  (lambdag@ (a : s c)
    (let ([ls1 (walk* (car (oc-rands oc)) s)]
          [ls2 (walk* (cadr (oc-rands oc)) s)]
          [out (walk* (caddr (oc-rands oc)) s)])
      ((conde
        ((== ls1 '()) 
         (== ls2 out))
        ((fresh (a d res)
           (appendo d ls2 res)
           (== ls1 `(,a . , d))
           (== out `(,a . ,res)))))
       a))))

(define (do-enforce-appendo x)
  (lambdag@ (a : s c)
    (let ([ocs (filter/rator 'append-c c)])
      (cond
        [(null? ocs) a]
        [else
         ((let loop ([ocs ocs])
            (cond
              [(null? ocs)
               (do-enforce-appendo x)]
              [else 
               (lambdag@ (a : s c)
                 ((fresh () 
                    (enforce-appendo (car ocs))
                    (loop (cdr ocs)))
                  (make-a s (remq (car ocs) c))))]))
          a)]))))

(extend-enforce-fns 'appendo do-enforce-appendo)
