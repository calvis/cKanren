#lang racket

;; Based on code written by Nada Amin
;; See: https://github.com/namin/clpset-miniKanren

(require "ck.rkt" "tree-unify.rkt"
         (rename-in (only-in "neq.rkt" =/=) [=/= =/=-other])
         (only-in rackunit check-equal?))
(provide set seto set-var normalize empty-set make-set
         enforce-lazy-unify-same =/= lazy-unify-same
         enforce-lazy-union-set lazy-union-set uniono
         enforce-lazy-union-var lazy-union-var disjo !disjo
         !ino ino !uniono)

;; == DATA STRUCTURES ==========================================================

;; a set-var, a variable that can only be bound to a set
(define-var-type set-var "s"
  #:methods gen:unifiable
  [(define (compatible? u v s c)
     (or (var? v) (set? v)))
   (define (gen-unify u v e s c)
     (cond
      [(var? v) 
       (unify e (ext-s v u s) c)]
      [else (unify-set v u e s c)]))])

;; a set structure, where left is a list, and right is another set.
;; for example {1 2} = (set '(1) (set '(2) (empty-set)))
(struct set (left right)
  #:transparent
  #:methods gen:mk-struct
  [(define (recur s k)
     (k (set-left s) (set-right s)))
   (define (constructor s) set)
   (define (override-occurs-check? s) #t)
   (define (reify-mk-struct s r) 
     (reify-set (normalize s) r))]
  #:methods gen:unifiable
  [(define (compatible? set v s c)
     (or (var? v) (set? v)))
   (define (gen-unify set v e s c)
     (unify-set set v e s c))]
  #:methods gen:custom-write
  [(define (write-proc set port mode)
     (cond
      [(empty-set? set) (display "∅" port)]
      [else 
       (display "{" port)
       (for ([x (set-left set)])
            (display " " port) (display x port))
       (display " | " port)
       (display (set-right set) port)
       (display " }" port)]))])

;; returns the list equivalent of s
(define (reify-set s r)
  (cond
   [(empty-set? s) s]
   [else
    (define sl (sort (map (lambda (t) (reify-term t r)) (set-left s)) lex<=))
    (define sr (reify-term (set-right s) r))
    (set sl sr)]))

(define (empty-set) 
  (set #f #f))

(define (empty-set? x) 
  (and (set? x)
       (not (set-left x)) 
       (not (set-right x))))

;; normalizes (aka flattens) the set:
;; (normalize (set '(1) (set '(2) (empty-set)))) 
;; => (set '(1 2) (empty-set))
(define (normalize s)
  (cond
   [(var? s) s]
   [(set-var? s) s]
   [(empty-set? s) s]
   [(null? (set-left s)) 
    (normalize (set-right s))]
   [else
    (let ([sl (sort (set-left s) lex<=)]
          [sr (normalize (set-right s))])
      (cond
       [(set-var? sr) (set sl sr)]
       [(empty-set? sr) (set sl sr)]
       [else (set (sort (append sl (set-left sr)) lex<=)
                  (set-right sr))]))]))

;; checks membership in a set
(define (set-member? x st)
  (cond
   [(empty-set? st) #f]
   [else (memq x (set-left st))]))

(define (same-set? s s^)
  (cond
   [(eq? s s^) #t]
   [(not (set? s)) #f]
   [(not (set? s^)) #f]
   [(empty-set? s) (empty-set? s^)]
   [(empty-set? s^) #f]
   [(equal? (set-left s) (set-left s^))
    (same-set? (set-right s) (set-right s^))]
   [else #f]))

(define (tail s)
  (cond
   [(empty-set? s) s]
   [(set-var? s) s]
   [else (tail (set-right s))]))

(define (update-set set s) 
  (normalize (walk* set s)))

;; == UNIFICATION ==============================================================

;; unifis a set u and a term v
(define (unify-set u v e s c)
  (unify e s (ext-c (build-oc safe-unify-set u v) c)))

(define (safe-unify-set u v)
  (conj
   (seto u)
   (seto v)
   (unify-well-formed-sets u v)))

(define (unify-well-formed-sets X T)
  (constraint
   #:package (a : s c)
   (let ([X (update-set X s)]
         [T (update-set T s)])
     (cond
      [(same-set? X T) succeed]
      [(and (not (set? X)) (set? T))
       (unify-well-formed-sets T X)]
      ;; it is possible normalization gave us two set-vars
      [(and (set-var? X) (set-var? T))
       (== X T)]
      [(set? T)
       (cond
        [(or (empty-set? X) (empty-set? T)) fail]
        [(set-member? X T) fail]
        [(same-set? (set-right X) (set-right T))
         (lazy-unify-same X T)]
        [else (lazy-unify-diff X T)])]
      [(set-var? T)
       (cond
        [(same-set? (set-right X) T)
         (let ([N (set-var (gensym 'n-unify))])
           (conj
            (proper-set (set (set-left X) N))
            (unify-well-formed-sets (set (set-left X) N) T)))]
        [else (update-s T X)])]
      [else fail]))))

(define (lazy-unify-same X T)
  (constraint
   #:package (a : s c) 
   (let ([X (update-set X s)]
         [T (update-set T s)])
     (cond
      [(null? (set-left X))
       (unify-walked (set-right X) T)]
      [(and (set? T) (null? (set-left T)))
       (unify-walked (set-right T) X)]
      [else (update-c-nocheck (build-oc lazy-unify-same X T))]))))

(define (lazy-unify-diff X T)
  (constraint
   #:package (a : s c) 
   (let ([X (update-set X s)]
         [T (update-set T s)])
     (cond
      [(null? (set-left X))
       (== T (set-right X))]
      [(null? (set-left T))
       (== X (set-right T))]
      ;; if there's only one thing in X or T, gtfo
      [(or (and (empty-set? (set-right X))
                (null? (cdr (set-left X))))
           (and (empty-set? (set-right T))
                (null? (cdr (set-left T)))))
       (conj
        (== (set-left  X) (set-left T))
        (== (set-right X) (set-right T)))]
      [else (update-c-nocheck (build-oc lazy-unify-diff X T))]))))

;; =============================================================================

;; X = {t|s} = {t'|s'} = T
(define (enforce-lazy-unify-diff oc)
  (constraint
   #:package (a : s c)
   (let ([X (update-set (car (oc-rands oc)) s)]
         [T (update-set (cadr (oc-rands oc)) s)])
     (let/set ([(x X^) X]
               [(t T^) T])
       (conde
        [(== x t)
         (conde
          [(== X^ T^)]
          [(== (set `(,x) X^) T^)
           (!ino x X^)]
          [(== X^ (set `(,t) T^))
           (!ino t T^)])]
        [(fresh (n)
           (proper-seto n)
           (== X^ (set `(,t) n))
           (!ino t n)
           (== (set `(,x) n) T^)
           (!ino x n))])))))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}
(define (enforce-lazy-unify-same oc)
  (constraint 
   #:package (a : s c)
   (let ([X (update-set (car (oc-rands oc)) s)]
         [T (update-set (cadr (oc-rands oc)) s)])
     (let ([t0  (car (set-left X))]
           [ts  (set-left X)]
           [t^s (set-left T)]
           [M   (set-right X)])
       (let loop ([tjs (set-left T)])
         (cond
          [(null? tjs) fail]
          [else
           (let ([tj (car tjs)])
             (conde
              [(== t0 tj)
               (!ino t0 M)
               (!ino tj M)
               (conde
                [(== (set (cdr ts) M) (set (rem1 tj t^s) M))]
                [(== (set ts M) (set (rem1 tj t^s) M))]
                [(== (set (cdr ts) M) (set t^s M))])]
              ;; M = {t0 | N}, {t1 .. tm | N} = {t'0 .. t'n | N}
              [(fresh (N N^)
                 (proper-seto N)
                 (proper-seto N^)
                 (== M (set `(,t0) N))
                 (!ino t0 N)
                 (== N (set (cdr ts) N^))
                 (== (set (cdr ts) N^)
                     (set t^s N)))]
              [(loop (cdr tjs))]))]))))))

(define (enforce-set-cs x)
  (conj
   (loop 'union-fresh enforce-one-union-fresh)
   (loop 'disjoint-fresh enforce-one-disjoint-fresh)
   (cycle)))

(define (cycle)
  (conj
    (loop 'in-set            enforce-in)
    (loop 'lazy-unify-same enforce-lazy-unify-same)
    (loop 'lazy-unify-diff enforce-lazy-unify-diff)
    (loop 'lazy-neq-sets   enforce-lazy-neq-sets)
    (loop 'lazy-neq-var    enforce-lazy-neq-var)
    (loop 'lazy-union-var  enforce-lazy-union-var)
    (loop 'lazy-union-set  enforce-lazy-union-set)
    ;; (loop 'lazy-union-neq  enforce-lazy-union-neq)
    (loop 'lazy-!union     enforce-!union)
    (constraint
     #:package (a : s c)
     (cond
      [(null? (filter-memq/rator
               '(in-set
                 lazy-unify-same
                 lazy-unify-diff
                 lazy-neq-sets
                 lazy-neq-var
                 lazy-union-var
                 lazy-union-set
                 lazy-union-neq
                 lazy-!union
                 disjoint)
               c))
       succeed]
      [else (cycle)]))))

(define (loop sym fn)
  (constraint
   #:package (a : s c)
   (let ([ocs (filter/rator sym c)])
     (conj
      (replace-ocs sym '())
      (let inner ([ocs ocs])
        (cond
         [(null? ocs) 
          succeed]
         [else 
          (conj
           (fn (car ocs))
           (inner (cdr ocs)))]))))))

(define (rem1 x ls)
  (cond
   [(null? ls) ls]
   [(eq? (car ls) x) (cdr ls)]
   [else (cons (car ls) (rem1 x (cdr ls)))]))

(define (make-set ls)
  (if (null? ls)
      (empty-set)
      (set ls (empty-set))))

(define (seto u) 
  (constraint
   #:package (a : s c)
   (let ([u (walk u s)])
     (cond
      [(set-var? u) succeed]
      [(empty-set? u) succeed]
      [(set? u)
       (let loop ([l (set-left u)])
         (cond
          [(null? l)
           (seto (set-right u))]
          [(set? (car l))
           (conj
            (seto (car l))
            (loop (cdr l)))]
          [else (loop (cdr l))]))]
      [(var? u)
       (let ([u^ (set-var (var-x u))])
         (update-s u u^))]
      [else fail]))))

(define (ino t s)
  (conj (seto s) (in-set t s)))

(define (in-set x S)
  (constraint
   #:package (a : s c)
   (let ([x (walk x s)]
         [S (update-set S s)])
     (cond
      [(empty-set? S) fail]
      [(and (set? S) (memq x (set-left S))) succeed]
      [else (update-c-nocheck (build-oc in-set x S))]))))

(define (enforce-in oc)
  (constraint
   #:package (a : s c)
   (let ([x (walk (car (oc-rands oc)) s)]
         [S (update-set (cadr (oc-rands oc)) s)])
     (cond
      [(empty-set? S) fail]
      [(set? S)
       (let ([t (car (set-left S))]
             [rest (set (cdr (set-left S)) (set-right S))])
         (conde
          [(== x t)]
          [(=/= x t) 
           (ino x rest)]))]
       [else 
        (fresh (N)
          (proper-seto N)
          (== (set `(,x) N) S)
          (!ino x N))]))))

(define (one-of-terms x t*)
  (cond
   [(null? t*) fail]
   [else (conde [(== x (car t*))] [(one-of-terms x (cdr t*))])]))

(define (=/= u v)
  (neq-? u v))

(define (=/=-set u v)
  (conj
   (seto u)
   (seto v)
   (=/=-well-formed u v)))

(define (neq-? u v)
  (constraint
   #:package (a : s c)
   (let ([u (walk u s)]
         [v (walk v s)])
     (cond
      [(eq? u v) fail]
      [(and (or (set? u) (set-var? u))
            (or (set? v) (set-var? v)))
       (=/=-set u v)]
      [(or (and (not (var? v)) (not (set? v)))
           (and (not (var? u)) (not (set? u))))
       (=/=-other u v)]
      [else (update-c-nocheck (build-oc neq-? u v))]))))

;; unlike union, we don't know that U or V is a set
(define (=/=-well-formed U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(and (set? V) (set? U))
       (lazy-neq-sets U V)]
      [(set-var? U)
       (lazy-neq-var U V)]
      [(set-var? V)
       (lazy-neq-var V U)]
      [else fail]))))

(define (set-neq U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(same-set? U V) fail]
      [else (update-c-nocheck (build-oc set-neq U V))]))))

;; both U and V are sets: {s|r} != {u|t}
(define (lazy-neq-sets U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(same-set? U V) fail]
      [(empty-set? U) succeed]
      [(empty-set? V) succeed]
      ;; {|r} != {u|t}
      [(null? (set-left U))
       (lazy-neq-var (set-right U) V)]
      ;; {s|r} != {|t}
      [(null? (set-left U))
       (lazy-neq-var (set-right V) U)]
      [else (update-c-nocheck (build-oc lazy-neq-sets U V))]))))

;; U should be a set var, V might be a set or set var
(define (lazy-neq-var U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(same-set? U V) fail]
      [(set? U)
       (lazy-neq-sets U V)]
      ;; V = {t0 .. tn | t} where U != t
      [(and (set? V) 
            (not (empty-set? V))
            (memq U (set-left V))) 
       succeed]
      [else (update-c-nocheck (build-oc lazy-neq-var U V))]))))

;; U is a set var, and V might be a set or a set var
(define (enforce-lazy-neq-var oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)])
     (conde
      ;; V = {t0 .. tn | U} => U != {t0 .. tn|U}
      [(cond
        [(and (set? V)
              (same-set? U (set-right V)))
         (let loop ([ts (set-left V)])
           (cond
            [(null? ts) fail]
            [else 
             (conde
              [(!ino (car ts) U)]
              [(loop (cdr ts))])]))]
        [else fail])]
      ;; V = {t0 .. tn | t} where U != t
      [(set-neq U V)]))))

;; both U and V are sets
(define (enforce-lazy-neq-sets oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)])
     (fresh (x)
       (conde
        [(ino x U) (!ino x V)]
        [(ino x V) (!ino x U)])))))

(define (!ino x S)
  (conj (seto S) (!in-c x S)))

(define (!in-c x S)
  (constraint
   #:package (a : s c)
   (let ([x (walk* x s)]
         [S (update-set S s)])
     (cond
      [(empty-set? S) succeed]
      [(and (set-var? S) (set? x) 
            (occurs-check S (set-left x) s))
       succeed]
      [(set? S)
       (cond
        [(memq x (set-left S)) fail]
        [(and (not (var? x))
              (empty-set? (set-right S))
              (not (any/var? (set-left S)))
              (not (memq x (set-left S))))
         succeed]
        [else
         (conj
          (not-in-t* x (set-left S))
          (!in-c x (set-right S)))])]
      [else (update-c-nocheck (build-oc !in-c x S))]))))

(define (make-not-in-t* x t* s c)
  (cond
   [(null? t*) (cons s c)]
   [else (cons s (ext-c (not-in-t* x t*) c))]))

(define (not-in-t* x t*)
  (cond
   [(null? t*) identitym]
   [else
    (conj (neq-? x (car t*)) (not-in-t* x (cdr t*)))]))

(define (uniono u v w)
  (conj (seto u) (seto v) (seto w) (union-fresh u v w)))

;; W is a set var
(define (lazy-union-var U V W)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)]
         [W (update-set W s)])
     (cond
      [(set? W)
       (lazy-union-set U V W)]
      [(same-set? U V)
       (== W U)]
      [(empty-set? U)
       (== W V)]
      [(empty-set? V)
       (== W U)]
      [else 
       (conj
        ;; Not tested yet
        ;; (check-set-neq U)
        ;; (check-set-neq V)
        ;; (check-set-neq W)
        (update-c-nocheck (build-oc lazy-union-var U V W)))]))))

;; W is a set
(define (lazy-union-set U V W)
  (constraint 
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)]
         [W (update-set W s)])
     (cond
      [(empty-set? W)
       (conj (== U W) (== V W))]
      [(same-set? U V)
       (== U W)]
      [else (update-c-nocheck (build-oc lazy-union-set U V W))]))))

;; Untested
#;
(define (check-set-neq X)
  (lambdam@ (a : s c)
    (cond
     [(not (set-var? X)) a]
     [else
      (define-values (neqs rest)
        (partition (lambda (oc) 
                     (or (eq? (oc-rator oc) 'lazy-neq-var)
                         (eq? (oc-rator oc) 'set-neq)))
                   c))
      (define X-neqs (filter (lambda (oc) (eq? (car (oc-rands oc)) X)) neqs))
      (cond
       [(null? X-neqs) a]
       [else
        (define vars (map (compose cadr oc-rands) X-neqs))
        (define oc (build-oc lazy-union-neq X vars))
        ((update-c-nocheck oc) (make-a s rest))])])))

;; Untested
#;
(define (lazy-union-neq X X-neqs)
  (update-c-nocheck (build-oc lazy-union-neq X X-neqs)))

;; W should be a var
(define (enforce-lazy-union-var oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)]
         [W (update-set (caddr (oc-rands oc)) s)])
     (cond
      [(set? W)
       (enforce-lazy-union-set oc)]
      [(or (set? U) (set? V))
       (let ([U (if (not (set? U)) V U)]
             [V (if (not (set? U)) U V)])
         (let ([t (car (set-left U))]
               [ts (cdr (set-left U))]
               [m  (set-right U)])
           (conde
            [(== W (empty-set))
             (== V (empty-set))
             (== U (empty-set))]
            [(fresh (N)
               (== W (set `(,t) N))
               (proper-seto N)
               (!ino t N)
               (conde
                [(fresh (N1)
                   (proper-seto N1)
                   (== N1 (set ts m))
                   (!ino t N1)
                   (uniono N1 V N))]
                [(fresh (N1)
                   (proper-seto N1)
                   (== V (set `(,t) N1))
                   (!ino t N1)
                   (uniono U N1 N))]
                [(fresh (N1 N2)
                   (proper-seto N1)
                   (proper-seto N2)
                   (== N1 (set ts m))
                   (!ino t N1)
                   (== V (set `(,t) N2))
                   (!ino t N2)
                   (uniono N1 N2 N))]))])))]
      [else (union-fresh U V W)]))))

(define (enforce-one-union-fresh oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)]
         [W (update-set (caddr (oc-rands oc)) s)])
     (fresh (t) (union-var-cases t U V W)))))

;; U or V is a set, W is a var
(define (union-var-cases t-val U V W)
  (conde
   [(== W (empty-set))
    (== U (empty-set))
    (== V (empty-set))]
   [(fresh (t N)
      (== t t-val)
      (== W (set `(,t) N))
      (!ino t N)
      (conde
       [(fresh (N1)
          (proper-seto N1)
          (== U (set `(,t) N1))
          (!ino t N1)
          (uniono N1 V N))]
       [(fresh (N1)
          (proper-seto N1)
          (== V (set `(,t) N1))
          (!ino t N1)
          (uniono U N1 N))]
       [(fresh (N1 N2)
          (proper-seto N1)
          (proper-seto N2)
          (== U (set `(,t) N1))
          (!ino t N1)
          (== V (set `(,t) N2))
          (!ino t N2)
          (uniono N1 N2 N))]))]))

(define (proper-seto S)
  (conj (seto S) (proper-set S)))

(define (proper-set S)
  (constraint
   #:package (a : s c)
   (let ([S (update-set S s)])
     (cond
      ;; X = {t0 .. tn | N}
      [(empty-set? S) succeed]
      [(set? S)
       (conj
        (let loop ([t* (set-left S)])
          (cond
           [(null? t*) succeed]
           [else
            (conj
             (not-in-t* (car t*) (rem1 (car t*) (set-left S)))
             (!in-c (car t*) (set-right S))
             (loop (cdr t*)))]))
        (proper-set (set-right S)))]
      [else (update-c-nocheck (build-oc proper-set S))]))))

(define (union-fresh U V W)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)]
         [W (update-set W s)])
     (cond
      [(set? W)
       (lazy-union-set U V W)]
      [(or (set? U) (set? W))
       (lazy-union-var U V W)]
      [else (update-c-nocheck (build-oc union-fresh U V W))]))))

(define (split-set S)
  (unless (set? S)
    (error 'split-set "S is not a set"))
  (let ([l (set-left S)])
    (values (car l) (set (cdr l) (set-right S)))))

(define-syntax-rule (let/set ([(s S^) S] ...) body ...)
  (let-values ([(s S^) (split-set S)] ...) body ...))

;; W is a set
(define (enforce-lazy-union-set oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)]
         [W (update-set (caddr (oc-rands oc)) s)])
     (let ([t (car (set-left W))]
           [N (set (cdr (set-left W)) (set-right W))])
       (fresh (N1 N2)
         (!ino t N1)
         (conde
          [(== U (set `(,t) N1))
           (!ino t V)
           (uniono N1 V N)]
          [(== V (set `(,t) N1))
           (!ino t U)
           (uniono U N1 N)]
          [(== U (set `(,t) N1))
           (== V (set `(,t) N2))
           (!ino t N2)
           (uniono N1 N2 N)]))))))

#;
(define (enforce-lazy-union-neq oc)
  (constraint
   #:package (a : s c)
   (let ([Z (update-set (car (oc-rands oc)) s)]
          [t* (map (conj normalize walk*) (cadr (oc-rands oc)))])
      (let loop ([t* t*])
        (cond
         [(null? t*) succeed]
         [else 
          (fresh (N)
            (conde
             [(ino N Z)
              (!ino N (car t*))]
             [(ino N (car t*))
              (!ino N Z)]
             [(== Z (empty-set))
              (=/= (car t*) (empty-set))])
            (loop (cdr t*)))])))))

(define (disjo u v)
  (conj (seto u) (seto v) (disjoint-fresh u v)))

(define (disjoint-fresh U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(or (set? U) (set? V))
       (disjoint U V)]
      [else (update-c (build-oc disjoint-fresh U V))]))))

(define (enforce-one-disjoint-fresh oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)])
     (cond
      [(and (set-var? U)
            (set-var? V))
       (conde
        ;; X || X -> X == empty
        [(== U V)
         (== U (empty-set))
         (== V (empty-set))]
        ;; empty || t or t || empty -> succeed
        [(conde
          [(== U (empty-set))
           (=/= V (empty-set))]
          [(=/= U (empty-set))
           (== V (empty-set))])]
        ;; TODO
        [(fresh (u v U^ V^)
           (== U (set `(,u) U^))
           (== V (set `(,v) V^))
           (=/= u v)
           (!ino u V^)
           (!ino v U^)
           (disjoint-fresh U^ V^))])]
      [else (disjoint U V)]))))

(define (disjoint U V)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)])
     (cond
      [(same-set? U V)
       (conj
        (== U (empty-set))
        (== V (empty-set)))]
      [(or (empty-set? U)
           (empty-set? V))
       succeed]
      [(and (set? U) (set? V))
       (let ([t1 (car (set-left U))]
             [s1 (set (cdr (set-left U)) (set-right U))]
             [t2 (car (set-left V))]
             [s2 (set (cdr (set-left V)) (set-right V))])
         (conj
          (neq-? t1 t2)
          (!in-c t1 s2)
          (!in-c t2 s1)
          (disjoint s1 s2)))]
       [(set? U)
        (let ([t (car (set-left U))]
              [U^ (set (cdr (set-left U)) (set-right U))])
          (conj (!in-c t V) (disjoint U^ V)))]
       [(set? V)
        (let ([t (car (set-left V))]
              [V^ (set (cdr (set-left V)) (set-right V))])
          (conj (!in-c t U) (disjoint U V^)))]
       [else (update-c-nocheck (build-oc disjoint U V))]))))

(define (!uniono u v w)
  (conj (seto u) (seto v) (seto w) (lazy-!union u v w)))

(define (lazy-!union U V W)
  (constraint
   #:package (a : s c)
   (let ([U (update-set U s)]
         [V (update-set V s)]
         [W (update-set W s)])
     (update-c-nocheck (build-oc lazy-!union U V W)))))

(define (enforce-!union oc)
  (constraint
   #:package (a : s c)
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)]
         [W (update-set (caddr (oc-rands oc)) s)])
     (fresh (N)
       (conde
        [(!ino N U) (!ino N V)  (ino N W)]
        [ (ino N U)            (!ino N W)]
        [            (ino N V) (!ino N W)])))))

(define (!disjo u v)
  (fresh (n) (ino n u) (ino n v)))

(define (process-rands rands* r)
  (let ([rands* (map (lambda (rands) (map (lambda (t) (reify-term t r)) rands)) rands*)])
    (for/fold ([new '()])
              ([rand rands*])
       (cond
        [(member rand new) new]
        [else (cons rand new)]))))

(define reify-set-neq
  (default-reify '=/= '(set-neq neq-?) process-rands))

(define reify-set-not-in
  (default-reify '!in '(!in-c) process-rands))

(define reify-set-union
  (default-reify 'union '(union-fresh) process-rands))

(define reify-disjoint
  (default-reify 'disj '(disjoint-fresh) process-rands))

(extend-enforce-fns 'sets enforce-set-cs)
(extend-reify-fns 'set-neq reify-set-neq)
(extend-reify-fns 'set-not-in reify-set-not-in)
(extend-reify-fns 'set-union reify-set-union)
(extend-reify-fns 'set-disj reify-disjoint)


