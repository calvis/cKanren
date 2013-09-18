#lang racket

(require "helpers.rkt" "constraints.rkt")

(provide (all-defined-out))

;; == CONSTRAINT STORE =========================================================

;; wrapper for a constraint store
(struct constraint-store (c)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-constraint-store args))])

;; writes a constraint store
(define (write-constraint-store constraint-store port mode)
  (define fn (lambda (s) ((parse-mode mode) s port)))
  (define c (constraint-store-c constraint-store))
  (fn "#c(")
  (for ([(rator rands*) c])
    (unless (null? rands*)
      (fn (cons rator rands*))))
  (fn ")"))

;; an empty constraint store
(define empty-c (hasheq))

;; extends the constraint store c with oc
(define (ext-c new-oc c) 
  (match-define (oc rator rands) new-oc)
  (hash-update c rator (curry cons rands) '()))

(define (ext-c* ocs c)
  (for/fold ([c c]) ([oc ocs]) (ext-c oc c)))

;; checks if oc is in c
(define (memq-c oc c)
  (memq-c/internal (oc-rator oc) oc c))

(define (memq-c/internal tag oc c)
  (let ([ocs (filter/rator tag c)])
    (memq oc ocs)))

;; removes oc from c
(define (remq-c rator rands c) 
  (hash-update c rator (curry remove rands) '()))

;; removes all ocs in oc* from c
(define (remq*-c oc* c)
  (for/fold ([c c]) ([oc oc*]) (remq-c oc c)))

;; filters the constraint store
(define (filter/rator key c)
  (hash-ref c key '()))

(define (filter-not/rator sym c)
  (apply append (for/list ([key (remq sym (hash-keys c))]) (hash-ref c key '()))))

(define (filter-memq/rator symls c)
  (apply append (for/list ([key symls]) (hash-ref c key '()))))

(define (filter-not-memq/rator symls c)
  (apply append (for/list ([key (hash-keys c)])
                          (cond
                           [(memq key symls) '()]
                           [else (hash-ref c key '())]))))

(define (c->list c)
  (apply append (hash-values c)))

(define (filter-something/rator pred? c)
  (apply append (for/list ([(rator rands*) c])
                  (cond
                   [(pred? rator) (map (curry oc rator) rands*)]
                   [else '()]))))

