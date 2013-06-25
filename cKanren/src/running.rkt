#lang racket

(require )

;; == FIXPOINT =================================================================

;; fixed point algorithm given some variables x* that have changed,
;; and list of constraints c.  will rerun any constraints in c that
;; mention x*
(define (run-constraints c)
  (cond
   [(hash? c)
    (for/fold 
     ([rest identitym])
     ([(key ocs) c])
     (composem 
      (for/fold 
       ([fn identitym])
       ([oc ocs])
       (composem fn (rem/run oc)))
      rest))]
   [(list? c)
    (for/fold 
     ([rest identitym])
     ([oc c])
     (composem rest (rem/run oc)))]
   [else (error 'run-constraints "don't know how to run ~s" c)]))

(define (run-relevant-constraints x* c)
  (for/fold 
   ([rest identitym])
   ([(key ocs) c])
   (composem 
    (for/fold 
     ([fn identitym])
     ([oc ocs]
      #:when (any-relevant/var? (oc-rands oc) x*))
     (composem fn (rem/run oc)))
    rest)))

;; removes a constraint from the constraint store and then 
;; reruns it as if it was just being introduced (will add itself
;; back to the constraint store if it still is waiting on info)
(define (rem/run oc)
  (lambdam@/private (a : s c q t)
    (let ([ocs (constraint-store-c c)])
      (cond
       [(memq-c oc ocs)
        ((oc-proc oc)
         (let ([new-c (constraint-store (remq-c oc ocs))])
           (make-a s new-c q t)))]
       [else a]))))

