#lang racket

(require "ck.rkt" racket/generic)
(provide == unify unify-two gen:unifiable 
         unifiable? compatible gen-unify)

(define (== u v) 
  (goal-construct (unify `((,u . ,v)))))

;; oops unify is a constraint
(define (unify e)
  (cond
   [(null? e) 
    identitym]
   [else
    (composem
     (unify-two (caar e) (cdar e))
     (unify (cdr e)))]))

;; unifies two things, u and v
(define (unify-two u v)
  (lambdam@ (a : s c)
    (let ([u (walk u s)]
          [v (walk v s)])
      (cond
       [(eq? u v) a]
       [(and (unifiable? u)
             (unifiable? v)) 
        (bindm a 
         (composem
          (compatible u v)
          (compatible v u)
          (gen-unify u v)))]
       [else #f]))))

;; a generic that defines when things are unifiable!
(define-generics unifiable
  (compatible unifiable v)
  (gen-unify unifiable v)
  #:defaults 
  (;; vars are compatible with structs that it does not appear in, or
   ;; structs that override the occurs check (ex. sets).
   [var?
    (define (compatible u v)
      (lambdam@ (a : s c)
        (cond
         [(var? v)
          ((check-attributes u v) a)]
         [(and (mk-struct? v)
               (not (override-occurs-check? v))
               (occurs-check u v s))
          #f]
         [else a])))
    (define (gen-unify u v)
      (lambdam@ (a)
        (cond
         [(var? v) ((update-s u v) a)]
         [else ((unify-two v u) a)])))]
   ;; anything that is a default mk-struct will unify just fine if
   ;; unified with something of the same type
   [default-mk-struct?
    (define (compatible p v)
      (cond
       [(or (var? v) (same-default-type? p v))
        identitym]
       [else (lambdam@ (a) #f)]))
    (define (gen-unify u v)
      (mk-struct-unify u v))]
   ;; mostly for constants: stings, numbers, booleans, etc.
   ;; they unify if they are eq? or equal?
   [(lambda (x) #t)
    (define (compatible u v)
      (cond
       [(or (var? v) (eq? u v) (equal? u v))
        identitym]
       [else (lambdam@ (a) #f)]))
    (define (gen-unify u v)
      (cond
       [(var? v) (update-s v u)]
       [else identitym]))]))

;; unifies mk-structs that are the same type
(define (mk-struct-unify u v)
  (lambdam@ (a)
    (cond
     [(var? v) 
      ((update-s v u) a)]
     [else
      (recur u 
       (lambda (ua vd)
         (recur v
          (lambda (va vd)
            (bindm a
              (composem
               (unify-two ua va)
               (unify `((,va . ,vd)))))))))])))

;; returns #t if attributes are ok
(define (check-attributes u v)
  (lambdam@ (a : s c)
    (let ([ua (get-attributes u c)]
          [va (get-attributes v c)])
      (cond
       [(and (not ua) (not va)) a]
       [(and (or (not ua) 
                 (andmap (lambda (aoc) ((attr-oc-uw? aoc) v va)) ua))
             (or (not va) 
                 (andmap (lambda (aoc) ((attr-oc-uw? aoc) u ua)) va)))
        a]
       [else #f]))))


