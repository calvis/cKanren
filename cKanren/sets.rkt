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

;; == UNIFICATION ==============================================================

;; unifis a set u and a term v
(define (unify-set u v e s c)
  (unify e s (ext-c (build-oc safe-unify-set u v) c)))

(define (safe-unify-set u v)
  (conj
   (well-formed-set-c u)
   (well-formed-set-c v)
   (unify-well-formed-sets u v)))

(define (unify-well-formed-sets X T)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(same-set? X T) a]
       [(and (not (set? X)) (set? T))
        ((unify-well-formed-sets T X) a)]
       ;; it is possible normalization gave us two set-vars
       [(and (set-var? X) (set-var? T))
        ((== X T) a)]
       [(set? T)
        (cond
         [(or (empty-set? X) (empty-set? T)) mzerom]
         [(set-member? X T) mzerom]
         [(same-set? (set-right X) (set-right T))
          ((lazy-unify-same X T) a)]
         [else ((lazy-unify-diff X T) a)])]
       [(set-var? T)
        (cond
         [(same-set? (set-right X) T)
          (let ([N (set-var (gensym 'n-unify))])
            (bindm a
              (conj
               (proper-set-c (set (set-left X) N))
               (unify-well-formed-sets (set (set-left X) N) T))))]
         [else ((update-s T X) a)])]
       [else mzerom]))))

(define (lazy-unify-same X T)
  (lambdam@ (a : s c) 
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((unify-walked (set-right X) T) a)]
       [(and (set? T) (null? (set-left T)))
        ((unify-walked (set-right T) X) a)]
       [else ((update-c-nocheck (build-oc lazy-unify-same X T)) a)]))))

(define (lazy-unify-diff X T)
  (lambdam@ (a : s c) 
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((== T (set-right X)) a)]
       [(null? (set-left T))
        ((== X (set-right T)) a)]
       ;; if there's only one thing in X or T, gtfo
       [(or (and (empty-set? (set-right X))
                 (null? (cdr (set-left X))))
            (and (empty-set? (set-right T))
                 (null? (cdr (set-left T)))))
        (bindm a
          (conj
           (== (set-left  X) (set-left T))
           (== (set-right X) (set-right T))))]
       [else ((update-c-nocheck (build-oc lazy-unify-diff X T)) a)]))))

;; =============================================================================

;; X = {t|s} = {t'|s'} = T
(define (enforce-lazy-unify-diff oc)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* (car (oc-rands oc)) s))]
          [T (normalize (walk* (cadr (oc-rands oc)) s))])
      (let ([t  (car (set-left X))]
            [s  (set (cdr (set-left X)) (set-right X))]
            [t^ (car (set-left T))]
            [s^ (set (cdr (set-left T)) (set-right T))])
        ((conde
          [(== t t^)
           (conde
            [(== s s^)]
            [(== (set `(,t) s) s^)
             (!ino t s)]
            [(== s (set `(,t^) s^))
             (!ino t^ s^)])]
          [(fresh (n)
             (proper-seto n)
             (== s (set `(,t^) n))
             (!ino t^ n)
             (== (set `(,t) n) s^)
             (!ino t n))])
         a)))))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}
(define (enforce-lazy-unify-same oc)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* (car (oc-rands oc)) s))]
          [T (normalize (walk* (cadr (oc-rands oc)) s))])
      (let ([t0  (car (set-left X))]
            [ts  (set-left X)]
            [t^s (set-left T)]
            [M   (set-right X)])
        ((let loop ((tjs (set-left T)))
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
                ((fresh (N N^)
                   (proper-seto N)
                   (proper-seto N^)
                   (== M (set `(,t0) N))
                   (!ino t0 N)
                   (== N (set (cdr ts) N^))
                   (== (set (cdr ts) N^)
                       (set t^s N))))
                ((loop (cdr tjs)))))]))
         a)))))

(define (enforce-set-cs x)
  (lambdam@ (a)
    ((conj
       (loop 'union-fresh enforce-one-union-fresh)
       (cycle a))
     a)))

(define (cycle a)
  (conj
    (loop 'in-c            enforce-in)
    (loop 'lazy-unify-same enforce-lazy-unify-same)
    (loop 'lazy-unify-diff enforce-lazy-unify-diff)
    (loop 'lazy-neq-sets   enforce-lazy-neq-sets)
    (loop 'lazy-neq-var    enforce-lazy-neq-var)
    (loop 'lazy-union-var  enforce-lazy-union-var)
    (loop 'lazy-union-set  enforce-lazy-union-set)
    (loop 'lazy-union-neq  enforce-lazy-union-neq)
    (loop 'lazy-!union     enforce-!union)
    (loop 'disj-c          enforce-disj)
    (lambdam@ (a^ : s^ c^)
      (cond
       [(null? (filter-memq/rator
                '(in-c
                  lazy-unify-same
                  lazy-unify-diff
                  lazy-neq-sets
                  lazy-neq-var
                  lazy-union-var
                  lazy-union-set
                  lazy-union-neq
                  lazy-!union
                  disj-c)
                c^))
        a^]
       [else ((cycle a^) a^)]))))

(define (loop sym fn)
  (lambdam@ (a : s c)
    (let ([ocs (filter/rator sym c)])
      (bindm a
        (conj
         (replace-ocs sym '())
         (let inner ([ocs ocs])
           (cond
            [(null? ocs) identitym]
            [else 
             (conj
               (fn (car ocs))
               (inner (cdr ocs)))])))))))

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
  (well-formed-set-c u))

(define (well-formed-set-c u)
  (lambdam@ (a : s c)
    (let ([u (walk u s)])
      (cond
       [(set-var? u) a]
       [(empty-set? u) a]
       [(set? u)
        (bindm a
          (let loop ([l (set-left u)])
            (cond
             [(null? l)
              (well-formed-set-c (set-right u))]
             [(set? (car l))
              (conj
               (well-formed-set-c (car l))
               (loop (cdr l)))]
             [else (loop (cdr l))])))]
       [(var? u)
        (let ([u^ (set-var (var-x u))])
          ((update-s u u^) a))]
       [else mzerom]))))

(define (ino t s)
  (conj
   (well-formed-set-c s)
   (in-c t s)))

(define (in-c x S)
  (lambdam@ (a : s c)
    (let ([x (walk x s)]
          [S (normalize (walk* S s))])
      (cond
       [(empty-set? S) mzerom]
       [(and (set? S) (memq x (set-left S))) a]
       [else ((update-c-nocheck (build-oc in-c x S)) a)]))))

(define (enforce-in oc)
  (lambdam@ (a : s c)
    (let ([x (walk (car (oc-rands oc)) s)]
          [S (normalize (walk* (cadr (oc-rands oc)) s))])
      (cond
       [(empty-set? S) mzerom]
       [(set? S)
        (let ([t (car (set-left S))]
              [rest (set (cdr (set-left S)) (set-right S))])
          ((conj
             (conde
              [(== x t)]
              [(=/= x t) 
               (ino x rest)]))
           a))]
       [else 
        ((fresh (N)
           (proper-seto N)
           (== (set `(,x) N) S)
           (!ino x N))
         a)]))))

(define (one-of-terms x t*)
  (cond
   [(null? t*) fail]
   [else (conde [(== x (car t*))] [(one-of-terms x (cdr t*))])]))

(define (=/= u v)
  (neq-? u v))

(define (=/=-set u v)
  (conj
   (well-formed-set-c u)
   (well-formed-set-c v)
   (=/=-well-formed u v)))

(define (neq-? u v)
  (lambdam@ (a : s c)
    (let ([u (walk u s)]
          [v (walk v s)])
      (cond
       [(eq? u v) mzerom]
       [(and (or (set? u) (set-var? u))
             (or (set? v) (set-var? v)))
        ((=/=-set u v) a)]
       [(or (and (not (var? v)) (not (set? v)))
            (and (not (var? u)) (not (set? u))))
        ((=/=-other u v) a)]
       [else ((update-c-nocheck (build-oc neq-? u v)) a)]))))

;; unlike union, we don't know that U or V is a set
(define (=/=-well-formed U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(and (set? V) (set? U))
        ((lazy-neq-sets U V) a)]
       [(set-var? U)
        ((lazy-neq-var U V) a)]
       [(set-var? V)
        ((lazy-neq-var V U) a)]
       [else mzerom]))))

(define (set-neq U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V) mzerom]
       [else ((update-c-nocheck (build-oc set-neq U V)) a)]))))

;; both U and V are sets: {s|r} != {u|t}
(define (lazy-neq-sets U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V) mzerom]
       [(empty-set? U) a]
       [(empty-set? V) a]
       ;; {|r} != {u|t}
       [(null? (set-left U))
        ((lazy-neq-var (set-right U) V) a)]
       ;; {s|r} != {|t}
       [(null? (set-left U))
        ((lazy-neq-var (set-right V) U) a)]
       [else ((update-c-nocheck (build-oc lazy-neq-sets U V)) a)]))))

;; U should be a set var, V might be a set or set var
(define (lazy-neq-var U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V) mzerom]
       [(set? U)
        ((lazy-neq-sets U V) a)]
       ;; V = {t0 .. tn | t} where U != t
       [(and (set? V) 
             (not (empty-set? V))
             (memq U (set-left V))) 
        a]
       [else ((update-c-nocheck (build-oc lazy-neq-var U V)) a)]))))

;; U is a set var, and V might be a set or a set var
(define (enforce-lazy-neq-var oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))])
      (bindm a
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
         [(set-neq U V)])))))

;; both U and V are sets
(define (enforce-lazy-neq-sets oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))])
      ((fresh (x)
         (conde
          [(ino x U) (!ino x V)]
          [(ino x V) (!ino x U)]))
       a))))

(define (!ino x S)
  (conj
   (well-formed-set-c S)
   (!in-c x S)))

(define (!in-c x S)
  (lambdam@ (a : s c)
    (let ([x (walk* x s)]
          [S (normalize (walk* S s))])
      (cond
       [(empty-set? S) a]
       [(and (set-var? S) (set? x) 
             (occurs-check S (set-left x) s))
        a]
       [(set? S)
        (cond
         [(memq x (set-left S)) mzerom]
         [(and (not (var? x))
               (empty-set? (set-right S))
               (not (any/var? (set-left S)))
               (not (memq x (set-left S))))
          a]
         [else
          (bindm a
            (conj
             (not-in-t* x (set-left S))
             (!in-c x (set-right S))))])]
       [else ((update-c-nocheck (build-oc !in-c x S)) a)]))))

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
  (conj
   (well-formed-set-c u)
   (well-formed-set-c v)
   (well-formed-set-c w)
   (union-fresh u v w)))

;; W is a set var
(define (lazy-union-var U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      (cond
       [(set? W)
        (bindm a (lazy-union-set U V W))]
       [(same-set? U V)
        (bindm a (== W U))]
       [(empty-set? U)
        (bindm a (== W V))]
       [(empty-set? V)
        (bindm a (== W U))]
       [else 
        (bindm a
          (conj
           ;; Not tested yet
           ;; (check-set-neq U)
           ;; (check-set-neq V)
           ;; (check-set-neq W)
           (update-c-nocheck (build-oc lazy-union-var U V W))))]))))

;; W is a set
(define (lazy-union-set U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      (cond
       [(empty-set? W)
        (bindm a (conj (== U W) (== V W)))]
       [(same-set? U V)
        (bindm a (== U W))]
       [else (bindm a (update-c-nocheck (build-oc lazy-union-set U V W)))]))))

;; Untested
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
(define (lazy-union-neq X X-neqs)
  (update-c-nocheck (build-oc lazy-union-neq X X-neqs)))

;; W should be a var
(define (enforce-lazy-union-var oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))]
          [W (normalize (walk* (caddr (oc-rands oc)) s))])
      (cond
       [(set? W)
        ((enforce-lazy-union-set oc) a)]
       [(or (set? U) (set? V))
        (let ([U (if (not (set? U)) V U)]
              [V (if (not (set? U)) U V)])
          (let ([t (car (set-left U))]
                [ts (cdr (set-left U))]
                [m  (set-right U)])
            ((conde
              ((== W (empty-set))
               (== V (empty-set))
               (== U (empty-set)))
              ((fresh (N)
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
                     (uniono N1 N2 N))]))))
             a)))]
       [else (bindm a (union-fresh U V W))]))))

(define (enforce-one-union-fresh oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))]
          [W (normalize (walk* (caddr (oc-rands oc)) s))])
      ((fresh (t) (union-var-cases t U V W)) a))))

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
  (conj
   (well-formed-set-c S)
   (proper-set-c S)))

(define (proper-set-c S)
  (lambdam@ (a : s c)
    (let ([S (normalize (walk* S s))])
      (cond
       ;; X = {t0 .. tn | N}
       [(empty-set? S) a]
       [(set? S)
        ((conj
          (let loop ([t* (set-left S)])
            (cond
             [(null? t*) identitym]
             [else
              (conj
               (not-in-t* (car t*) (rem1 (car t*) (set-left S)))
               (!in-c (car t*) (set-right S))
               (loop (cdr t*)))]))
          (proper-set-c (set-right S)))
         a)]
       [else ((update-c-nocheck (build-oc proper-set-c S)) a)]))))

(define (union-fresh U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      (cond
       [(set? W)
        ((lazy-union-set U V W) a)]
       [(or (set? U) (set? W))
        ((lazy-union-var U V W) a)]
       [else ((update-c-nocheck (build-oc union-fresh U V W)) a)]))))

;; W is a set
(define (enforce-lazy-union-set oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))]
          [W (normalize (walk* (caddr (oc-rands oc)) s))])
      ((fresh (t N N1 N2)
         (== t (car (set-left W)))
         (== N (set (cdr (set-left W)) (set-right W)))
         (!ino t N)
         (!ino t N1)
         (conde
          [(== U (set `(,t) N1))
           (uniono N1 V N)]
          [(== V (set `(,t) N1))
           (uniono U N1 N)]
          [(== U (set `(,t) N1))
           (== V (set `(,t) N2))
           (!ino t N2)
           (uniono N1 N2 N)]))
       a))))

(define (enforce-lazy-union-neq oc)
  (lambdam@ (a : s c)
    (let ([Z (normalize (walk* (car (oc-rands oc)) s))]
          [t* (map (conj normalize walk*) (cadr (oc-rands oc)))])
      ((let loop ([t* t*])
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
             (loop (cdr t*)))]))
       a))))

(define (disjo u v)
  (conj
   (well-formed-set-c u)
   (well-formed-set-c v)
   (disj-c u v)))

(define (disj-c U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V)
        (bindm a
          (conj
           (== U (empty-set))
           (== V (empty-set))))]
       [(empty-set? U) a]
       [(empty-set? V) a]
       [(and (set? U) (set? V))
        (let ([t1 (car (set-left U))]
              [s1 (set (cdr (set-left U)) (set-right U))]
              [t2 (car (set-left V))]
              [s2 (set (cdr (set-left V)) (set-right V))])
          (bindm a
            (conj
             (neq-? t1 t2)
             (!in-c t1 s2)
             (!in-c t2 s1)
             (disj-c s1 s2))))]
       [(set? U)
        (let ([t (car (set-left U))]
              [U^ (set (cdr (set-left U)) (set-right U))])
          (bindm a
            (conj
             (!in-c t U^)
             (disj-c U^ V))))]
       [(set? V)
        (let ([t (car (set-left V))]
              [V^ (set (cdr (set-left V)) (set-right V))])
          (bindm a
            (conj
             (!in-c t V^)
             (disj-c U V^))))]
       [else ((update-c-nocheck (build-oc disj-c U V)) a)]))))

(define (enforce-disj oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))])
      (printf "enforce-disj: ~s ~s\n" U V)
      (cond
       [(and (set-var? U)
             (set-var? V))
        ((conde
          [(== U V)
           (== U (empty-set))
           (== V (empty-set))]
          [(fresh (u v U^ V^)
             (== U (set `(,u) U^))
             (== V (set `(,v) V^))
             (=/= u v)
             (!ino u V^)
             (!ino v U^)
             (disjo U^ V^))])
         a)]
       [else (oc-proc oc)]))))

(define (!uniono u v w)
  (conj
   (well-formed-set-c u)
   (well-formed-set-c v)
   (well-formed-set-c w)
   (lazy-!union u v w)))

(define (lazy-!union U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      ((update-c-nocheck (build-oc lazy-!union U V W)) a))))

(define (enforce-!union oc)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))]
          [W (normalize (walk* (caddr (oc-rands oc)) s))])
      ((fresh (N)
         (conde
          [(!ino N U) (!ino N V)  (ino N W)]
          [ (ino N U)            (!ino N W)]
          [            (ino N V) (!ino N W)]))
       a))))

(define (!disjo u v)
  (fresh (n)
    (ino n u)
    (ino n v)))

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

(extend-enforce-fns 'sets enforce-set-cs)
(extend-reify-fns 'set-neq reify-set-neq)
(extend-reify-fns 'set-not-in reify-set-not-in)
(extend-reify-fns 'set-union reify-set-union)



