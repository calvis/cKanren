#lang racket

;; Based on code written by Nada Amin
;; See: https://github.com/namin/clpset-miniKanren

(require cKanren/ck cKanren/tree-unify
         (rename-in (only-in cKanren/neq =/= subsumes?) [=/= =/=-other])
         (only-in rackunit check-equal?)
         cKanren/src/framework cKanren/src/events)
(provide set seto set-var normalize empty-set make-set
         enforce-lazy-unify-same =/= lazy-unify-same
         enforce-lazy-union-set lazy-union-set uniono
         enforce-lazy-union-var lazy-union-var disjo !disjo
         !in ino !uniono define-set-constraint)

;; == DATA STRUCTURES ==========================================================

;; a set-var, a variable that can only be bound to a set
(define-var-type set-var "s"
  #:methods gen:unifiable
  [(define (compatible? u v s c e)
     (or (var? v) (set? v)))
   (define (gen-unify u v p s c e)
     (cond
      [(var? v) 
       (unify p (ext-s v u s) c e)]
      [else (unify-set v u p s c e)]))])

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
  [(define (compatible? set v s c e)
     (or (var? v) (set? v)))
   (define (gen-unify set v p s c e)
     (unify-set set v p s c e))]
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
   [(symbol? s) s]
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

(define (update-set set s . rest) 
  (normalize (apply walk* set s rest)))

(define-constraint-type set-constraint update-set)

;; == UNIFICATION ==============================================================

;; unifis a set u and a term v
(define (unify-set u v e s c)
  (unify e s (ext-c (safe-unify-set u v) c)))

(define-constraint (safe-unify-set u v)
  (conj
   (seto u)
   (seto v)
   (unify-well-formed-sets u v)))

(define-set-constraint (unify-well-formed-sets X T)
  (cond
   [(same-set? X T) succeed]
   [(and (not (set? X)) (set? T))
    (unify-well-formed-sets T X)]
   ;; it is possible normalization gave us two set-vars
   [(and (set-var? X) (set-var? T))
    (== X T)]
   [(set? T)
    (cond
     [(or (empty-set? X) 
          (empty-set? T)
          (set-member? X T))
      fail]
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
     [else (add-association T X)])]
   [else fail]))

(define-set-constraint (lazy-unify-same X T)
  #:reaction
  [(enforce (list X T))
   (enforce-lazy-unify-same X T)]
  #:package (a [s c e])
  (cond
   [(null? (set-left X))
    (unify-walked (set-right X) T)]
   [(and (set? T) (null? (set-left T)))
    (unify-walked (set-right T) X)]
   [else (add-constraint (lazy-unify-same X T))]))

(define-set-constraint (lazy-unify-diff X T)
  #:reaction
  [(enforce (list X T))
   (enforce-lazy-unify-diff X T)]
  #:package (a [s c e])
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
   [else (add-constraint (lazy-unify-diff X T))]))

;; =============================================================================

;; X = {t|s} = {t'|s'} = T
(define (enforce-lazy-unify-diff X T)
  (let/set ([(x X^) X] [(t T^) T])
    (conde
     [(== x t)
      (conde
       [(== X^ T^)]
       [(== (set `(,x) X^) T^)
        (!in x X^)]
       [(== X^ (set `(,t) T^))
        (!in t T^)])]
     [(fresh (n)
        (proper-seto n)
        (!in t n)
        (!in x n)
        (== X^ (set `(,t) n))
        (== (set `(,x) n) T^))])))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}

(define (enforce-lazy-unify-same X T)
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
            (!in t0 M)
            (!in tj M)
            (conde
             [(== (set (cdr ts) M) (set (rem1 tj t^s) M))]
             [(== (set ts M) (set (rem1 tj t^s) M))]
             [(== (set (cdr ts) M) (set t^s M))])]
           ;; M = {t0 | N}, {t1 .. tm | N} = {t'0 .. t'n | N}
           [(fresh (N N^)
              (proper-seto N)
              (proper-seto N^)
              (!in t0 N)
              (== M (set `(,t0) N))
              (== N (set (cdr ts) N^))
              (== (set (cdr ts) N^)
                  (set t^s N)))]
           [(loop (cdr tjs))]))]))))

#;
(define (enforce-set-cs x)
  (conj
   (loop 'union-fresh enforce-one-union-fresh)
   (loop 'disjoint-fresh enforce-one-disjoint-fresh)
   (cycle)))

#;
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
    (transformer
     #:package (a [s c e])
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
  (transformer
   #:package (a [s c e])
   (let ([ocs (filter/rator sym c)])
     (conj
      ;; (replace-ocs sym '()) TODO
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
  (if (null? ls) (empty-set) (set ls (empty-set))))

(define-constraint (seto u) 
  (cond
   [(or (set-var? u) (empty-set? u)) succeed]
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
      (add-association u u^))]
   [else fail]))

(define (ino t s)
  (conj (seto s) (in-set t s)))

(define-set-constraint (in-set [x walk] S)
  (cond
   [(empty-set? S) fail]
   [(and (set? S) (memq x (set-left S))) succeed]
   [else (add-constraint (in-set x S))]))

#;
(define (enforce-in oc)
  (transformer
   #:package (a [s c e])
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
          (!in x N))]))))

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

(define-constraint (neq-? u v)
  #:reification-function
  (lambda (ans r)
    (values '=/= (cons u v)))
  (cond
   [(eq? u v) fail]
   [(and (or (set? u) (set-var? u))
         (or (set? v) (set-var? v)))
    (=/=-set u v)]
   [(or (and (not (var? v)) (not (set? v)))
        (and (not (var? u)) (not (set? u))))
    (=/=-other u v)]
   [else (add-constraint (neq-? u v))]))

(define-constraint-interaction neq-?-subsume
  [(neq-? u v) (neq-? u^ v^)]
  #:package (a [s c e])
  [(subsumes? (list (cons u v)) (list (cons u^ v^)) c)
   [(neq-? u v)]])

;; unlike union, we don't know that U or V is a set
(define-set-constraint (=/=-well-formed U V)
  (cond
   [(and (set? V) (set? U))
    (lazy-neq-sets U V)]
   [(set-var? U)
    (lazy-neq-var U V)]
   [(set-var? V)
    (lazy-neq-var V U)]
   [else fail]))

(define-set-constraint (set-neq U V)
  (cond
   [(same-set? U V) fail]
   [else (add-constraint (set-neq U V))]))

;; both U and V are sets: {s|r} != {u|t}
(define-set-constraint (lazy-neq-sets U V)
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
   [else (add-constraint (lazy-neq-sets U V))]))

;; U should be a set var, V might be a set or set var
(define-set-constraint (lazy-neq-var U V)
  (cond
   [(same-set? U V) fail]
   [(set? U)
    (lazy-neq-sets U V)]
   ;; V = {t0 .. tn | t} where U != t
   [(and (set? V) 
         (not (empty-set? V))
         (memq U (set-left V))) 
    succeed]
   [else (add-constraint (lazy-neq-var U V))]))

;; U is a set var, and V might be a set or a set var
#;
(define (enforce-lazy-neq-var oc)
  (transformer
   #:package (a [s c e])
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
              [(!in (car ts) U)]
              [(loop (cdr ts))])]))]
        [else fail])]
      ;; V = {t0 .. tn | t} where U != t
      [(set-neq U V)]))))

;; both U and V are sets
#;
(define (enforce-lazy-neq-sets oc)
  (constraint
   #:package (a [s c e])
   (let ([U (update-set (car (oc-rands oc)) s)]
         [V (update-set (cadr (oc-rands oc)) s)])
     (fresh (x)
       (conde
        [(ino x U) (!in x V)]
        [(ino x V) (!in x U)])))))

(define-set-constraint (!in [x walk] S)
  #:package (a [s c e])
  #:reified
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
       (!in x (set-right S)))])]
   [else (add-constraint (!in x S))]))

(define-constraint-interaction
  !in-unique
  [(!in x S) (!in x S)] => [(!in x S)])

(define (make-not-in-t* x t* s c)
  (cond
   [(null? t*) (cons s c)]
   [else (cons s (ext-c (not-in-t* x t*) c))]))

(define (not-in-t* x t*)
  (cond
   [(null? t*) succeed]
   [else (conj (neq-? x (car t*)) (not-in-t* x (cdr t*)))]))

(define (uniono u v w)
  (conj (seto u) (seto v) (seto w) (union-fresh u v w)))

;; W is a set var
(define-set-constraint (lazy-union-var U V W)
  #:reaction
  [(enforce (list U V W))
   (enforce-lazy-union-var U V W)]
  #:package (a [s c e])
  (printf "lazy-union-var: ~a ~a ~a\n" U V W)
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
     (add-constraint (lazy-union-var U V W)))]))

;; W is a set
(define-set-constraint (lazy-union-set U V W)
  #:reaction
  [(enforce (list U V W))
   (enforce-lazy-union-set U V W)]
  #:package (a [s c e])
  (cond
   [(empty-set? W)
    (conj (== U W) (== V W))]
   [(same-set? U V)
    (== U W)]
   [else (add-constraint (lazy-union-set U V W))]))

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
(define-set-constraint (enforce-lazy-union-var U V W)
  #:package (a [s c e])
  (printf "enforce-lazy-union-var: ~a ~a ~a ~a\n" U V W a)
  (cond
   [(set? W)
    (enforce-lazy-union-set U V W)]
   [(or (set? U) (set? V))
    ;; U must be a set
    (let ([U (if (set? U) U V)]
          [V (if (set? U) V U)])
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
            (!in t N)
            (conde
             [(fresh (N1)
                (proper-seto N1)
                (== N1 (set ts m))
                (!in t N1)
                (uniono N1 V N))]
             [(fresh (N1)
                (proper-seto N1)
                (== V (set `(,t) N1))
                (!in t N1)
                (constraint
                 #:package (a [s c e])
                 (printf "<=====================\n")
                 (pretty-print a)
                 (printf "=====================>\n")
                 fail)
                (uniono U N1 N))]
             [(fresh (N1 N2)
                (proper-seto N1)
                (proper-seto N2)
                (!in t N1)
                (!in t N2)
                (== N1 (set ts m))
                (== V (set `(,t) N2))
                (uniono N1 N2 N))]))])))]
   [else (union-fresh U V W)]))

#;
(define (enforce-one-union-fresh oc)
  (constraint
   #:package (a [s c e])
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
      (!in t N)
      (conde
       [(fresh (N1)
          (proper-seto N1)
          (== U (set `(,t) N1))
          (!in t N1)
          (uniono N1 V N))]
       [(fresh (N1)
          (proper-seto N1)
          (== V (set `(,t) N1))
          (!in t N1)
          (uniono U N1 N))]
       [(fresh (N1 N2)
          (proper-seto N1)
          (proper-seto N2)
          (== U (set `(,t) N1))
          (!in t N1)
          (== V (set `(,t) N2))
          (!in t N2)
          (uniono N1 N2 N))]))]))

(define (proper-seto S)
  (conj (seto S) (proper-set S)))

(define-set-constraint (proper-set S)
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
          (!in (car t*) (set-right S))
          (loop (cdr t*)))]))
     (proper-set (set-right S)))]
   [else (add-constraint (proper-set S))]))

(define-set-constraint (union-fresh U V W)
  (printf "union-fresh: ~a ~a ~a\n" U V W)
  (cond
   [(set? W)
    (lazy-union-set U V W)]
   [(or (set? U) (set? W))
    (lazy-union-var U V W)]
   [else (add-constraint (union-fresh U V W))]))

(define (split-set S)
  (unless (set? S)
    (error 'split-set "S is not a set"))
  (let ([l (set-left S)])
    (values (car l) (set (cdr l) (set-right S)))))

(define-syntax-rule (let/set ([(s S^) S] ...) body ...)
  (let-values ([(s S^) (split-set S)] ...) body ...))

;; W is a set
(define-set-constraint (enforce-lazy-union-set U V W)
  #:package (a [s c e])
  (let ([t (car (set-left W))]
        [N (set (cdr (set-left W)) (set-right W))])
    (fresh (N1 N2)
      (!in t N1)
      (conde
       [(== U (set `(,t) N1))
        (!in t V)
        (uniono N1 V N)]
       [(== V (set `(,t) N1))
        (!in t U)
        (uniono U N1 N)]
       [(== U (set `(,t) N1))
        (== V (set `(,t) N2))
        (!in t N2)
        (uniono N1 N2 N)]))))

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
              (!in N (car t*))]
             [(ino N (car t*))
              (!in N Z)]
             [(== Z (empty-set))
              (=/= (car t*) (empty-set))])
            (loop (cdr t*)))])))))

(define (disjo u v)
  (conj (seto u) (seto v) (disjoint-fresh u v)))

(define-set-constraint (disjoint-fresh U V)
  (cond
   [(or (set? U) (set? V))
    (disjoint U V)]
   [else (add-constraint (disjoint-fresh U V))]))

#;
(define (enforce-one-disjoint-fresh oc)
  (constraint
   #:package (a [s c e])
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
           (!in u V^)
           (!in v U^)
           (disjoint-fresh U^ V^))])]
      [else (disjoint U V)]))))

(define-set-constraint (disjoint U V)
  (cond
   [(same-set? U V)
    (conj
     (== U (empty-set))
     (== V (empty-set)))]
   [(or (empty-set? U)
        (empty-set? V))
    succeed]
   [(and (set? U) (set? V))
    (let/set ([(t1 s1) U]
              [(t2 s2) V])
      (conj
       (neq-? t1 t2)
       (!in t1 s2)
       (!in t2 s1)
       (disjoint s1 s2)))]
   [(set? U)
    (let/set ([(u U^) U])
      (conj (!in u V) (disjoint U^ V)))]
   [(set? V)
    (let/set ([(v V^) V])
      (conj (!in v U) (disjoint U V^)))]
   [else (add-constraint (disjoint U V))]))

(define (!uniono u v w)
  (conj 
   (seto u) (seto v) (seto w)
   (fresh (t)
     (conde
      [(!in t u) (!in t v)  (ino t w)]
      [ (ino t u)            (!in t w)]
      [            (ino t v) (!in t w)]))))

(define (!disjo u v)
  (fresh (n) (ino n u) (ino n v)))

(define (process-rands rands* r)
  (let ([rands* (map (lambda (rands) (map (lambda (t) (reify-term t r)) rands)) rands*)])
    (for/fold ([new '()])
              ([rand rands*])
       (cond
        [(member rand new) new]
        [else (cons rand new)]))))

;; (define reify-set-neq
;;   (default-reify '=/= '(set-neq neq-?) process-rands))
;; 
;; (define reify-set-not-in
;;   (default-reify '!in '(!in-c) process-rands))
;; 
;; (define reify-set-union
;;   (default-reify 'union '(union-fresh) process-rands))
;; 
;; (define reify-disjoint
;;   (default-reify 'disj '(disjoint-fresh) process-rands))

;; (extend-enforce-fns 'sets enforce-set-cs)
;; (extend-reify-fns 'set-neq reify-set-neq)
;; (extend-reify-fns 'set-not-in reify-set-not-in)
;; (extend-reify-fns 'set-union reify-set-union)
;; (extend-reify-fns 'set-disj reify-disjoint)


