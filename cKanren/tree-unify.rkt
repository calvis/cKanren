#lang racket

(require "ck.rkt" racket/generic)
(provide == unify gen:unifiable gen-unify compatible? unify-two unify-walked unifiable?)

;; a generic that defines when things are unifiable!
(define-generics unifiable
  (compatible? unifiable v s c)
  (gen-unify unifiable v e s c)
  #:defaults 
  (;; vars are compatible with structs that it does not appear in, or
   ;; structs that override the occurs check (ex. sets).
   [var?
    (define (compatible? u v s c)
      (and (check-attributes u v s c)
           (cond
            [(mk-struct? v)
             (or (override-occurs-check? v)
                 (not (occurs-check u v s)))]
            [else #t])))
    (define (gen-unify u v e s c)
      (cond
       [(var? v) (unify e (ext-s u v s) c)]
       [else (unify-walked v u e s c)]))]
   ;; anything that is a default mk-struct will unify just fine if
   ;; unified with something of the same type
   [default-mk-struct?
    (define (compatible? p v s c)
      (or (var? v) (same-default-type? p v)))
    (define (gen-unify u v e s c)
      (mk-struct-unify u v e s c))]
   ;; mostly for constants: strings, numbers, booleans, etc.
   ;; they unify if they are eq? or equal?
   [(lambda (x) #t)
    (define (compatible? u v s c)
      (or (var? v) (eq? u v) (equal? u v)))
    (define (gen-unify u v e s c)
      (cond
       [(var? v) (unify e (ext-s v u s) c)]
       [else (unify e s c)]))]))

(define (== u v)
  (constraint
   #:package (a [s c e])
   (cond
    [(unify `((,u . ,v)) s c)
     => (lambda (s/c)
          (update-package (car s/c) (cdr s/c)))]
    [else fail])))

(define (unify e s c)
  (cond
   [(null? e) (cons s c)]
   [else (unify-two (caar e) (cdar e) (cdr e) s c)]))

;; unifies two things, u and v
(define-syntax-rule (unify-two u v e s c)
  (let ([u^ (walk u s)] [v^ (walk v s)])
    (cond
     [(and (var? u^) (not (var? u^)))
      (unify-walked v^ u^ e s c)]
     [else (unify-walked u^ v^ e s c)])))

(define (unify-walked u v e s c)
  (cond
   [(eq? u v) (unify e s c)]
   [else
    (and (unifiable? u)
         (unifiable? v)
         (compatible? u v s c)
         (compatible? v u s c)
         (gen-unify u v e s c))]))

;; unifies mk-structs that are the same type
(define (mk-struct-unify u v e s c)
  (cond
   [(var? v) (unify e (ext-s v u s) c)]
   [else
    (recur u 
     (lambda (ua ud)
       (recur v
        (lambda (va vd)
          (unify-two ua va `((,ud . ,vd) . ,e) s c)))))]))

;; returns #t if attributes are ok
(define (check-attributes u v s c)
  (let ([ua (get-attributes u c)]
        [va (get-attributes v c)])
    (and (or (not ua) (no-conflicts? v va ua))
         (or (not va) (no-conflicts? u ua va)))))

(define (no-conflicts? u ua va)
  (andmap (lambda (aoc) ((attr-oc-uw? aoc) u ua)) va))

