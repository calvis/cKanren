#lang racket

;; Based on code written by Nada Amin
;; See: https://github.com/namin/clpset-miniKanren

(require "ck.rkt" "tree-unify.rkt" "tester.rkt"
         (rename-in (only-in "neq.rkt" =/=-c) [=/=-c =/=-other]))
(provide set seto)

;; a set-var, a variable that can only be bound to a set
(define-var-type set-var "s"
  #:methods gen:unifiable
  [(define (compatible u v)
     (lambdam@ (a : s c)
       (cond
        [(or (var? v) (set? v)) a]
        [else #f])))
   (define (gen-unify u v)
     (lambdam@ (a)
       (cond
         [(var? v) ((update-s v u) a)]
         [(set? v) ((unify-set v u) a)]
         [else #f])))])

;; a set structure, where left is a list, and right is another set.
;; for example {1 2} = (set '(1) (set '(2) (empty-set)))
(struct set (left right)
  #:transparent
  #:methods gen:mk-struct
  [(define (recur s k)
     (k (set-left s) (set-right s)))
   (define (constructor s) set)
   (define (override-occurs-check? s) #t)
   (define (mk-struct->sexp s)
     (set->sexp (normalize s)))]
  #:methods gen:unifiable
  [(define (compatible s v)
     (lambdam@ (a)
       (cond
        [(or (var? v) (set? v)) a]
        [else #f])))
   (define (gen-unify s v)
     (unify-set s v))]
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
(define (set->sexp s)
  (define (term->sexp t) 
    (cond
     [(set? t) (set->sexp t)]
     [(mk-struct? t) (mk-struct->sexp t)]
     [else t]))
  (cond
   [(empty-set? s) '∅]
   [else
    (define sl (sort (map term->sexp (set-left s)) lex<=))
    (define r  (set-right s))
    (define sr (or (and (set? r) (set->sexp r)) r))
    (cond
     [(null? sl)
      (cond
       [(var? sr) sr]
       [else (cadr sr)])]
     [(or (var? sr) (symbol? sr))
      `(set (,@sl : ,sr))]
     [else `(set (,@sl : . ,(cadr sr)))])]))

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
    (let ([s-l (sort (set-left s) lex<=)]
          [s-r (normalize (set-right s))])
      (cond
       [(set-var? s-r)
        (set s-l s-r)]
       [(empty-set? s-r)
        (set s-l s-r)]
       [else 
        (set (sort (append s-l (set-left s-r)) lex<=)
             (set-right s-r))]))]))

(module+ test
  (let ([n (set-var 'n)])
    (test "normalize 1" (normalize (set '() n)) n))

  (test "normalize 2"
        (normalize (set '(bird cat) (set '() (empty-set))))
        (set '(bird cat) (empty-set))))

;; checks membership in a set
(define (set-member? x st)
  (cond
   [(empty-set? st) #f]
   [else (memq x (set-left st))]))

;; unifis a set u and a term v
(define (unify-set u v)
  (composem 
   (well-formed-set-c u)
   (well-formed-set-c v)
   (unify-well-formed-sets u v)))

;; unifies two well formed sets
(define (unify-well-formed-sets X T)
   (lambdam@ (a : s c)
     (let ((X (normalize (walk* X s)))
           (T (normalize (walk* T s))))
       (cond
        [(same-set? X T) a]
        [(and (not (set? X)) (set? T))
         ((unify-well-formed-sets T X) a)]
        ;; it is possible normalization gave us two set-vars?
        [(and (set-var? X) (set-var? T))
         ((unify-two X T) a)]
        [(set? T)
         (cond
          [(or (empty-set? X) (empty-set? T)) #f]
          [(set-member? X T) #f]
          [(same-set? (set-right X) (set-right T))
           ((lazy-unify-same X T) a)]
          [else ((lazy-unify-diff X T) a)])]
        [(set-var? T)
         (cond
          [(same-set? (set-right X) T)
           (let ([N (set-var (gensym 'n-unify))])
             (bindm a 
               (composem 
                (proper-seto (set (set-left X) N))
                (unify-well-formed-sets (set (set-left X) N) T))))]
          [else ((update-s T X) a)])]
        [else #f]))))

;; lazily unions two sets with different tails
;; X = {t|s} = {t'|s'} = T
(define (lazy-unify-diff X T)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((unify-two T (set-right X)) a)]
       [(null? (set-left T))
        ((unify-two X (set-right T)) a)]
       [(same-set? (tail X) (tail T))
        ((lazy-unify-same X T) a)]
       ;; if there's only one thing in X or T, gtfo
       [(or (and (empty-set? (set-right X))
                 (null? (cdr (set-left X))))
            (and (empty-set? (set-right T))
                 (null? (cdr (set-left T)))))
        (bindm a
          (composem
           (unify-two (set-left  X) (set-left  T))
           (unify-two (set-right X) (set-right T))))]
       [else ((update-c-nocheck (build-oc lazy-unify-diff X T)) a)]))))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}
(define (lazy-unify-same X T)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((unify-two (set-right X) T) a)]
       [(and (set? T) (null? (set-left T)))
        ((unify-two (set-right T) X) a)]
       [else ((update-c-nocheck (build-oc lazy-unify-same X T)) a)]))))

;; X = {t|s} = {t'|s'} = T
(define (enforce-lazy-unify-diff oc)
  (lambdag@ (a : s c)
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
  (lambdag@ (a : s c)
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

(define (enforce-set-cs x)
  (lambdag@ (a)
    ((fresh ()
       (loop 'union-fresh enforce-one-union-fresh)
       (cycle a))
     a)))

(define (cycle a)
  (fresh ()
    (loop 'in-c            enforce-in)
    (loop 'lazy-unify-same enforce-lazy-unify-same)
    (loop 'lazy-unify-diff enforce-lazy-unify-diff)
    (loop 'lazy-neq-sets   enforce-lazy-neq-sets)
    (loop 'lazy-neq-var    enforce-lazy-neq-var)
    (loop 'lazy-union-var  enforce-lazy-union-var)
    (loop 'lazy-union-set  enforce-lazy-union-set)
    (loop 'lazy-union-neq  enforce-lazy-union-neq)
    (loop 'lazy-!union     enforce-!union)
    (lambdag@ (a^ : s^ c^)
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
                  lazy-!union)
                c^))
        a^]
       [else ((cycle a^) a^)]))))

(define (loop sym fn)
  (lambdag@ (a : s c)
    (let ([ocs (filter/rator sym c)])
      ((fresh ()
         (goal-construct
          (replace-ocs sym '()))
         (let inner ([ocs ocs])
           (cond
            [(null? ocs) 
             unitg]
            [else 
             (fresh () 
               (fn (car ocs))
               (inner (cdr ocs)))])))
       a))))

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
  (goal-construct (well-formed-set-c u)))

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
              (composem
               (well-formed-set-c (car l))
               (loop (cdr l)))]
             [else (loop (cdr l))])))]
       [(var? u)
        (let ([u^ (set-var (var-x u))])
          ((update-s u u^) a))]
       [else #f]))))

(define (ino t s)
  (goal-construct 
   (composem
    (well-formed-set-c s)
    (in-c t s))))

(define (in-c x S)
  (lambdam@ (a : s c)
    (let ([x (walk x s)]
          [S (normalize (walk* S s))])
      (cond
       [(empty-set? S) #f]
       [(and (set? S) (memq x (set-left S))) a]
       [else ((update-c-nocheck (build-oc in-c x S)) a)]))))

(define (enforce-in oc)
  (lambdag@ (a : s c)
    (let ([x (walk (car (oc-rands oc)) s)]
          [S (normalize (walk* (cadr (oc-rands oc)) s))])
      (cond
       [(empty-set? S) #f]
       [(set? S)
        (let ([t (car (set-left S))]
              [rest (set (cdr (set-left S)) (set-right S))])
          ((fresh ()
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
  (goal-construct (neq-? u v)))

(define (=/=-set u v)
  (composem
   (well-formed-set-c u)
   (well-formed-set-c v)
   (=/=-well-formed u v)))

(define (neq-? u v)
  (lambdam@ (a : s c)
    (let ([u (walk u s)]
          [v (walk v s)])
      (cond
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
       [else #f]))))

(define (set-neq U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V) #f]
       [else ((update-c-nocheck (build-oc set-neq U V)) a)]))))

;; both U and V are sets: {s|r} != {u|t}
(define (lazy-neq-sets U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V) #f]
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
       [(same-set? U V) #f]
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
  (lambdag@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))])
      ((conde
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
         [(goal-construct (set-neq U V))])
       a))))

;; both U and V are sets
(define (enforce-lazy-neq-sets oc)
  (lambdag@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))])
      ((fresh (x)
         (conde
          [(ino x U) (!ino x V)]
          [(ino x V) (!ino x U)]))
       a))))

(define (!ino x S)
  (goal-construct 
   (composem
    (well-formed-set-c S)
    (!in-c x S))))

(define (!in-c x S)
  (lambdam@ (a : s c)
    (let ([x (walk* x s)]
          [S (normalize (walk* S s))])
      ;; (printf "!in-c: ~s ~s\n" x S)
      (cond
       [(empty-set? S) a]
       [(and (set-var? S) (set? x) 
             (occurs-check S (set-left x) s))
        a]
       [(set? S)
        (cond
         [(memq x (set-left S)) #f]
         [(and (not (var? x))
               (empty-set? (set-right S))
               (not (any/var? (set-left S)))
               (not (memq x (set-left S))))
          a]
         [else
          (bindm a
            (composem
             (not-in-t* x (set-left S))
             (!in-c x (set-right S))))])]
       [else ((update-c-nocheck (build-oc !in-c x S)) a)]))))

(define (not-in-t* x t*)
  (cond
   [(null? t*) identitym]
   [else
    (composem (neq-? x (car t*)) (not-in-t* x (cdr t*)))]))

(define (uniono u v w)
  (goal-construct
   (composem
    (well-formed-set-c u)
    (well-formed-set-c v)
    (well-formed-set-c w)
    (union-fresh u v w))))

;; W is a set var
(define (lazy-union-var U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      (cond
       [(set? W)
        ((lazy-union-set U V W) a)]
       [(same-set? U V)
        ((unify-two W U) a)]
       [(empty-set? U)
        ((unify-two W V) a)]
       [(empty-set? V)
        ((unify-two W U) a)]
       [else 
        (bindm a
          (composem
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
        ((composem (unify-two U W) (unify-two V W)) a)]
       [(same-set? U V)
        ((unify-two U W) a)]
       [else ((update-c-nocheck (build-oc lazy-union-set U V W)) a)]))))

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
  (lambdag@ (a : s c)
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
                   (uniono N1 N2 N))])) 
             a)))]
       [else ((goal-construct (union-fresh U V W)) a)]))))

(define (enforce-one-union-fresh oc)
  (lambdag@ (a : s c)
    (let ([U (normalize (walk* (car (oc-rands oc)) s))]
          [V (normalize (walk* (cadr (oc-rands oc)) s))]
          [W (normalize (walk* (caddr (oc-rands oc)) s))])
      ((fresh (t) (union-var-cases t U V W)) a))))

;; U or V is a set, W is a var
(define (union-var-cases t-val U V W)
  (fresh (t N)
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
        (uniono N1 N2 N))])))

(define (proper-seto S)
  (goal-construct 
   (composem
    (well-formed-set-c S)
    (proper-set-c S))))

(define (proper-set-c S)
  (lambdam@ (a : s c)
    (let ([S (normalize (walk* S s))])
      (cond
       ;; X = {t0 .. tn | N}
       [(empty-set? S) a]
       [(set? S)
        ((composem
          (let loop ([t* (set-left S)])
            (cond
             [(null? t*) identitym]
             [else
              (composem
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
  (lambdag@ (a : s c)
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
  (lambdag@ (a : s c)
    (let ([Z (normalize (walk* (car (oc-rands oc)) s))]
          [t* (map (composem normalize walk*) (cadr (oc-rands oc)))])
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
  (goal-construct
   (composem
    (well-formed-set-c u)
    (well-formed-set-c v)
    (disj-c u v))))

(define (disj-c U V)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))])
      (cond
       [(same-set? U V)
        (bindm a
          (composem
           (unify-well-formed-sets U (empty-set))
           (unify-well-formed-sets V (empty-set))))]
       [(empty-set? U) a]
       [(empty-set? V) a]
       [(and (set? U) (set? V))
        (let ([t1 (car (set-left U))]
              [s1 (set (cdr (set-left U)) (set-right U))]
              [t2 (car (set-left V))]
              [s2 (set (cdr (set-left V)) (set-right V))])
          (bindm a
            (composem
             (neq-? t1 t2)
             (!in-c t1 s2)
             (!in-c t2 s1)
             (disj-c s1 s2))))]
       [(set? U)
        (let ([t1 (car (set-left U))]
              [t2 (set (cdr (set-left U)) (set-right U))])
          (bindm a
            (composem
             (!in-c t1 t2)
             (disj-c t2 V))))]
       [(set? V)
        (let ([t1 (car (set-left V))]
              [t2 (set (cdr (set-left V)) (set-right V))])
          (bindm a
            (composem
             (!in-c t1 t2)
             (disj-c t2 U))))]
       [else ((update-c-nocheck (build-oc disj-c U V)) a)]))))

(define (!uniono u v w)
  (goal-construct
   (composem
    (well-formed-set-c u)
    (well-formed-set-c v)
    (well-formed-set-c w)
    (lazy-!union u v w))))

(define (lazy-!union U V W)
  (lambdam@ (a : s c)
    (let ([U (normalize (walk* U s))]
          [V (normalize (walk* V s))]
          [W (normalize (walk* W s))])
      ((update-c-nocheck (build-oc lazy-!union U V W)) a))))

(define (enforce-!union oc)
  (lambdag@ (a : s c)
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

(define (process-rands rands*)
  (let ([rands* (map (lambda (rands) (map format-rand rands)) rands*)])
    (for/fold ([new '()])
              ([rand rands*])
       (cond
        [(member rand new) new]
        [else (cons rand new)]))))

(define (format-rand rand)
  (cond
   [(mk-struct? rand)
    (mk-struct->sexp rand)]
   [else rand]))

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

(module+ test
  (test "test 0.0" (run* (q) succeed)  '(_.0))
  (test "test 0.1" (run* (q) (== 5 5)) '(_.0))
  (test "test 0.2" (run* (q) (== 5 6)) '())
  (test "test 0.3" (run* (q) (fresh (x) (== q `(,x)))) '((_.0)))

  (test "test 1"
        (run* (q) (== (empty-set) (empty-set)))
        '(_.0))

  (test "test 2" 
        (run* (q) (== (make-set '(1)) (make-set '(1))))
        '(_.0))

  (test "test 3.0"
        (run* (q) (== (empty-set) 5))
        '())

  (test "test 3.1"
        (run* (q) (== 5 (empty-set)))
        '())

  (test "test 4.0"
        (run* (q) (== (make-set '(1)) 5))
        '())

  (test "test 4.1"
        (run* (q) (== 5 (make-set '(1))))
        '())

  (test "test 5.0"
        (run* (q) (== (make-set '(1)) (empty-set)))
        '())

  (test "test 5.05"
        (run* (q) (== (make-set '(1)) (make-set '(2))))
        '())

  (test "test 5.1"
        (run* (q) (== (make-set '(2)) (make-set '(1))))
        '())

  (test "test 6.01"
        (run* (q) (== q (empty-set)))
        '(∅))

  (test "test 6.02"
        (run* (q) (== (empty-set) q))
        '(∅))

  (test "test 6.1"
        (run* (q) (== q (make-set '(1 2))))
        '((set (1 2 : ∅))))

  (test "test 7"
        (run* (q) 
          (== q (make-set '(1)))
          (== q (make-set '(2))))
        '())
  
  (test "test 8.0"
        (run* (q) (== q (set '(1) q)))
        `(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 8.1"
        (run* (q) (== (set '(1) q) q))
        `(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 9.0"
        (run* (q) (fresh (z) (== q (set `(,z) q))))
        '(((set (_.0 : s.1)) : (!in (_.0 s.1)))))

  (test "test 9.1"
        (run* (q) (fresh (z) (== q (set '(1) z))))
        '((set (1 : s.0))))

  (test "test 9.2"
        (run* (q) (fresh (z) (== q (set `(,(set '(1) z)) q))))
        '(((set ((set (1 : s.0)) : s.1)) : (!in ((set (1 : s.0)) s.1)))))

  (test "test 9.5"
        (run* (q) 
          (== (set `(1) q) (set `(2) (empty-set))))
        '())

  (test "enforce-lazy-unify-same"
        (run* (q)
          (seto q)
          (enforce-lazy-unify-same (build-oc lazy-unify-same (set `(1) q) (set `(2) q))))
        '(((set (1 2 : s.0)) : (!in (1 s.0) (2 s.0)))))

  (test "test 10.0"
        (run* (q) 
          (== (set `(1) q) (set `(2) q)))
        '(((set (1 2 : s.0)) : (!in (1 s.0) (2 s.0)))))

  (test "test 10.01"
        (run* (q) 
          (fresh (x y r s) 
            (== (set `(1) r) (set `(2) s))))
        '(_.0))

  (test "test 10.05"
        (run 1 (q) 
          (fresh (x y r)
            (== (set `(,x) r) (set `(,y) r))))
        '(_.0))
  
  (test "test 10.06"
        (run* (q)
          (== q (set '() (set '(1) q))))
        '(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 10.07"
        (run* (q)
          (== (set '() q) (set '() q)))
        '(s.0))

  (test "test 10.08" 
        (run* (q)
          (== q (set '() q)))
        '(s.0))

  (test "test 10.09"
        (run* (q)
          (== (set '() (set '() q)) (set '() q)))
        '(s.0))

  (test "test 9.iv.1"
        (run* (q)
          (== (set `(1) (set `(2) (empty-set)))
              (set `(2) (set `(1) (empty-set)))))
        `(_.0))

  (test "test 10.2"
        (run* (q) 
          (fresh (y r s) 
            (== (set `(,q) r) (set `(,y) s))))
        '(_.0 _.0 _.0 _.0))

  (test "test 10.3"
        (run* (q) 
          (fresh (x y r s) 
            (== q `(,x ,r ,y ,s))
            (== (set `(,x) r) (set `(,y) s))))
        '((_.0 s.1 _.0 s.1)
          ((_.0 (set (_.1 : s.2)) _.1 (set (_.0 : s.2))) : (!in (_.0 s.2) (_.1 s.2)))
          ((_.0 s.1 _.0 (set (_.0 : s.1))) : (!in (_.0 s.1)))
          ((_.0 (set (_.0 : s.1)) _.0 s.1) : (!in (_.0 s.1)))))

  (test "test 20"
        (run* (q)
          (=/= (empty-set) (empty-set)))
        '())

  (test "test 21"
        (run* (q)
          (=/= (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "test 22"
        (run* (q)
          (=/= q (empty-set)))
        '((_.0 : (=/= (_.0 ∅)))))

  (test "test 23"
        (run* (q) 
          (=/= q (set `(1) (set `(2) (empty-set)))))
        '((_.0 : (=/= (_.0 (set (1 2 : ∅)))))))

  (test "enforce-lazy-union-set"
        (run* (q)
          (enforce-lazy-union-set
           (build-oc lazy-union-set
                     (make-set '(1))
                     (make-set '(2))
                     (make-set '(1 2)))))
        '(_.0))

  ;; Sanity checks
  (test "sanity check 1"
        (run* (q) (uniono (empty-set) (empty-set) (empty-set)))
        '(_.0))
  
  (test "sanity check 2"
        (run* (q)
          (fresh (x y z)
            (uniono (set `(1) (empty-set)) 
                    (set `(1) (empty-set))
                    (set `(1) (empty-set)))))
        '(_.0))

  (test "test 26"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) (make-set '(1 2))))
        '(_.0))

  (test "test 27"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) (make-set '(3))))
        '())

  (test "test 28"
        (run* (q)
          (uniono q (make-set '(2)) (make-set '(1 2))))
        '((set (1 : ∅)) 
          (set (1 2 : ∅))))

  (test "test 29"
        (run* (q)
          (uniono (make-set '(1)) q (make-set '(1 2))))
        '((set (2 : ∅)) 
          (set (1 2 : ∅))))

  (test "test 30"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) q))
        '((set (1 2 : ∅))))

  (test "test 30.5"
        (run* (q) 
          (fresh (x y z v)
            (== q `(,x ,y ,z ,v))
            (uniono (make-set `(,x)) (set `(,y) z) v)))
        '(((_.0 _.1 s.2 (set (_.0 _.1 : s.2))) 
           : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1)))
          ((_.0 _.0 s.1 (set (_.0 : s.1)))
           : (!in (_.0 s.1)))
          ((_.0 _.1 (set (_.0 : s.2)) (set (_.0 _.1 : s.2)))
           : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1))) 
          ((_.0 _.0 (set (_.0 : s.1)) (set (_.0 : s.1)))
           : (!in (_.0 s.1)))))

  (test "test 31"
        (run* (q)
          (fresh (x y)
            (== q (make-set `(,x ,y)))
            (== (make-set `(,x ,y)) (make-set '(cat bird)))))
        '((set (bird cat : ∅)) (set (bird cat : ∅))))

  ;; Wrong?
  (test "test 32.15"
        (run* (q)
          (fresh (x y z)
            (uniono (make-set `(cat ,x)) (make-set `(bird ,y)) q)))
        '(((set (bird cat _.1 _.0 : ∅))
           : (=/= (_.0 _.1)) (=/= ((bird . _.0)) ((bird . _.1)) ((cat . _.0)) ((cat . _.1))))
          ((set (bird cat _.0 : ∅)) : (=/= ((bird . _.0)) ((cat . _.0))))
          (set (bird cat : ∅))
          ((set (bird cat _.0 : ∅)) : (=/= ((bird . _.0)) ((cat . _.0))))
          ((set (bird cat _.0 : ∅)) : (=/= ((bird . _.0)) ((cat . _.0))))
          (set (bird cat : ∅))))

  (test "enforce-lazy-union-var 1"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(dog))
            (make-set '(dog))
            q)))
        '((set (dog : ∅))))

  (test "enforce-lazy-union-var 2"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(dog cat))
            (make-set '(dog cat))
            q)))
        '((set (cat dog : ∅))))

  (test "enforce-lazy-union-var 3"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(cat dog))
            (make-set '(dog cat))
            q)))
        '((set (cat dog : ∅))))

  (test "enforce-lazy-union-var 4"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(cat dog bird))
            (make-set '(bird dog cat))
            q)))
        '((set (bird cat dog : ∅))))
  
  (test "union fresh"
        (run* (q)
          (fresh (x y z)
            (== q `(,x ,y ,z))
            (uniono x y z)
            (=/= z (empty-set))))
        '((((set (_.0 : s.1)) s.2 (set (_.0 : s.3))) 
           : (!in (_.0 s.1) (_.0 s.3)) (union (s.1 s.2 s.3)))
          ((s.0 (set (_.1 : s.2)) (set (_.1 : s.3))) 
           : (!in (_.1 s.2) (_.1 s.3)) (union (s.0 s.2 s.3)))
          (((set (_.0 : s.1)) (set (_.0 : s.2)) (set (_.0 : s.3))) 
           : (!in (_.0 s.1) (_.0 s.2) (_.0 s.3)) (union (s.1 s.2 s.3)))))

  (test "david's example"
        (time
         (length
          (run* (q)
            (fresh (x y z a b s s^)
              (== q s^)
              (uniono (make-set `(cat ,x ,y)) (make-set `(dog bird ,z)) s)
              (uniono s (make-set `(zebra ,a ,b)) s^)
              (== x 'dog)
              (== y 'bird)
              (== z 'cat)
              prt))))
        (length
         (run* (q)
           (fresh (x y z a b s s^)
             (== q s^)
             (uniono (make-set `(cat dog bird)) (make-set `(dog bird cat)) s)
             (uniono s (make-set `(zebra ,a ,b)) s^)
             prt))))

  ;; disj

  (test "disjo 1"
        (run* (q) (disjo (empty-set) (empty-set)))
        '(_.0))

  (test "disjo 2"
        (run* (q) (disjo (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "disjo 3"
        (run* (q) (disjo (empty-set) q))
        '(s.0))

  (test "disjo 4"
        (run* (q) (disjo (set '(1) (empty-set)) (set '(1) (empty-set))))
        '())
  
  (test "test disjo 1"
        (run* (q)
          (fresh (x y z)
            (== q `(,x ,y ,z))
            (disjo (set `(,x ,y) (empty-set)) (set '(a) z))))
        '(((_.0 _.1 s.2) : (!in (_.1 s.2)) (=/= ((a . _.0)) ((a . _.1))))))

  ;; !uniono

  (test "!uniono 1"
        (run* (q)
          (!uniono (empty-set) (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "!uniono 2"
        (run* (q)
          (!uniono (empty-set) (empty-set) (empty-set)))
        '())

  (test "ino"
        (run* (q)
          (ino q (set '(a b) (empty-set))))
        '(a b))

  (test "!ino 1"
        (run* (q)
          (!ino q (set '(a b) (empty-set))))
        '((_.0 : (=/= ((a . _.0)) ((b . _.0))))))

  (test "!uniono 3"
        (run* (q) 
          (!uniono (set `(x) (empty-set))
                   (set `(y) (empty-set))
                   (set `(,q) (empty-set))))
        '((_.0 : (=/= ((x . _.0)) ((y . _.0))))
          (_.0 : (=/= ((x . _.0))))
          (_.0 : (=/= ((y . _.0))))))

  (test "!uniono 4"
        (run 1 (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))))

  (test "!uniono 5"
        (run 5 (q)
          (fresh (x y)
            (!uniono q (empty-set) (set `(a b) (empty-set)))))
        '(((set (_.0 : s.1)) : (!in (_.0 s.1)) (=/= ((a . _.0)) ((b . _.0))))
          (s.0 : (!in (a s.0))) 
          (s.0 : (!in (b s.0)))))

  (test "!uniono 6"
        (run 5 (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))
          (((set (_.0 : s.1)) s.2) : (!in (_.0 s.1)) (=/= ((a . _.0)) ((b . _.0))))
          ((s.0 (set (_.1 : s.2))) : (!in (_.1 s.2)) (=/= ((a . _.1)) ((b . _.1))))
          ((s.0 s.1) : (!in (b s.0) (b s.1)))))

  (test "!uniono 7"
        (run* (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))
          (((set (_.0 : s.1)) s.2) : (!in (_.0 s.1)) (=/= ((a . _.0)) ((b . _.0))))
          ((s.0 (set (_.1 : s.2))) : (!in (_.1 s.2)) (=/= ((a . _.1)) ((b . _.1))))
          ((s.0 s.1) : (!in (b s.0) (b s.1)))))
  
)

