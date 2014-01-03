#lang racket

(require "constraints.rkt")

;; == CONSTRAINT STORE =========================================================
;; 
;; A ConstraintStore is a [Hasheq Rator [List-of Rands]]

(provide
 ;; Value -> Boolean
 ;; returns #t iff the value is a ConstraintStore (superfluously)
 constraint-store?

 ;; ConstraintStore
 ;; an empty ConstraintStore
 empty-c

 ;; Oc ConstraintStore -> ConstraintStore
 ;; adds oc to the constraint store 
 ext-c

 ;; Oc ConstraintStore -> ConstraintStore
 ;; removes the oc from the constraint store
 remq-c

 ;; ConstraintStore ConstraintStore -> [List-of Ocs]
 prefix-c
 
 ;; Rator ConstraintStore -> [List-of Rands]
 ;; returns all the rands that have rator as a key
 filter/rator

 ;; [List-of Rator] ConstraintStore -> [List-of Rands]
 ;; returns all the rands that have a rator in the given list
 filter-memq/rator

 ;; [Rator -> Boolean] ConstraintStore -> [List-of Oc]
 ;; it filters something?????
 filter-something/rator)

(define constraint-store? hash?)

(define empty-c (hasheq))

(define (ext-c new-oc c) 
  (match-define (oc rator rands) new-oc)
  (hash-update c rator (curry cons rands) '()))

(define (remq-c new-oc c) 
  (match-define (oc rator rands) new-oc)
  (hash-update c rator (curry remq rands) '()))

(define (prefix-c c c^)
  (for/fold 
   ([prefix '()])
   ([(rator rands*^) c^])
   (define rands* (hash-ref c rator '()))
   (define (prefix-loop rands*^ prefix)
     (cond
      [(eq? rands* rands*^) prefix]
      [else 
       (define new-prefix (cons (oc rator (car rands*^)) prefix))
       (prefix-loop (cdr rands*^) new-prefix)]))
   (prefix-loop rands*^ prefix)))

(define (filter/rator rator c)
  (hash-ref c rator '()))

(define (filter-memq/rator symls c)
  (apply append (for/list ([key symls]) (hash-ref c key '()))))

;; TODO: wow such name so good
(define (filter-something/rator pred? c)
  (apply append 
         (for/list ([(rator rands*) c])
           (cond
            [(pred? rator) 
             (map (curry oc rator) rands*)]
            [else '()]))))


