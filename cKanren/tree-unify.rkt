#lang cKanren

(require (except-in racket == string) racket/generic)

(require cKanren/attributes 
         cKanren/src/constraint-store
         cKanren/src/triggers
         cKanren/src/mk-structs
         (only-in cKanren/src/events
                  add-substitution-prefix-event  
                  empty-event))

(provide == unify unify-two unify-walked unify-change)
(provide gen:unifiable gen-unify compatible? unifiable?)

;; a generic that defines when things are unifiable!
(define-generics unifiable
  (compatible? unifiable v s c e)
  (gen-unify unifiable v p s c e)
  #:defaults 
  (;; vars are compatible with structs that it does not appear in, or
   ;; structs that override the occurs check (ex. sets).
   [var?
    (define (compatible? u v s c e)
      (and (check-attributes u v s c e) 
           (cond
            [(mk-struct? v)
             (or (override-occurs-check? v)
                 (not (occurs-check u v s)))]
            [else #t])))
    (define (gen-unify u v p s c e)
      (cond
       [(var? v) (unify p (ext-s u v s) c e)]
       [else (unify-walked v u p s c e)]))]
   ;; anything that is a default mk-struct will unify just fine if
   ;; unified with something of the same type
   [default-mk-struct?
    (define (compatible? p v s c e)
      (or (var? v) (same-default-type? p v)))
    (define (gen-unify u v p s c e)
      (mk-struct-unify u v p s c e))]
   ;; mostly for constants: strings, numbers, booleans, etc.
   ;; they unify if they are eq? or equal?
   [(lambda (x) #t)
    (define (compatible? u v s c e)
      (or (var? v) (eq? u v) (equal? u v)))
    (define (gen-unify u v p s c e)
      (cond
       [(var? v) (unify p (ext-s v (walk* u s c e) s) c e)]
       [else (unify p s c e)]))]))

(define (== u v)
  (transformer
   #:package (a [s c e])
   (cond
    [(unify `((,u . ,v)) s c e)
     => (match-lambda
          [(cons s c) (update-package s c)])]
    [else fail])))

(define (unify p s c e)
  (cond
   [(null? p) (cons s c)]
   [else (unify-two (caar p) (cdar p) (cdr p) s c e)]))

;; unifies two things, u and v
(define-syntax-rule (unify-two u v p s c e)
  (let ([u^ (walk u s c e)] [v^ (walk v s c e)])
    (cond
     [(and (var? u^) (not (var? u^)))
      (unify-walked v^ u^ p s c e)]
     [else (unify-walked u^ v^ p s c e)])))

(define (unify-walked u v p s c e)
  (cond
   [(eq? u v) (unify p s c e)]
   [else
    (and (unifiable? u)
         (unifiable? v)
         (compatible? u v s c e)
         (compatible? v u s c e)
         (gen-unify u v p s c e))]))

;; unifies mk-structs that are the same type
(define (mk-struct-unify u v p s c e)
  (cond
   [(var? v) (unify p (ext-s v (walk* u s c e) s) c e)]
   [else
    (recur u 
     (lambda (ua ud)
       (recur v
        (lambda (va vd)
          (unify-two ua va `((,ud . ,vd) . ,p) s c e)))))]))

(define (unify-new-prefix thing s c e)
  (match (unify (walk* thing s c e) s c e)
    [(cons s^ c^)
     (cons (prefix-s s s^) (prefix-c c c^))]
    [#f #f]))

(define-trigger (unify-change thing)
  #:package (a [s c e])
  [(add-substitution-prefix-event p)
   (=> abort)
   (unless (ormap (lambda (x) (memq (car x) (filter*/var? thing))) p)
     (abort))
   (unify-new-prefix thing s c e)]
  [(add-attribute-constraint-event rator (list x))
   (=> abort)
   (unless (memq x (filter*/var? thing))
     (abort))
   (unify-new-prefix thing s c e)]
  [(empty-event) ;; empty is not synonymous to new
   (unify-new-prefix thing s c e)])

