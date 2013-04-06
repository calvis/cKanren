#lang racket

;; Based on code written by Nada Amin
;; See: https://github.com/namin/clpset-miniKanren

(require "ck.rkt" "tree-unify.rkt" "tests/tester.rkt" "neq.rkt")

;; a set-var, a variable that can only be bound to a set
(define-cvar-type set-var "s"
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
   (define (constructor s)
     (lambda (a d) 
       (set a d)))
   (define (override-occurs-check? s) #t)
   (define (mk-struct->sexp s)
     (cond
      [(empty-set? s) '(set ())]
      [else 
       (let ([l (set-left s)]
             [r (set-right s)])
         (cond
          [(null? (set-left s))
           (cond
            [(symbol? r) r]
            [else (cadr r)])]
          [(symbol? r) `(set (,@l ,r))]
          [else `(set (,@l . ,(cadr r)))]))]))]
  #:methods gen:unifiable
  [(define (compatible s v)
     (lambdam@ (a)
       (cond
        [(or (var? v) (set? v)) a]
        [else #f])))
   (define (gen-unify s v)
     (unify-set s v))])

(define (empty-set) 
  (set #f #f))

(define (empty-set? x) 
  (and (set? x)
       (not (set-left x)) 
       (not (set-right x))))

;; normalizes (aka flattens) the set:
;; (normalize (set '(1) (set '(2) (empty-set)))) 
;; => (set '(1 2) (empty-set))
(define (normalize st)
  (cond
   [(var? st) st]
   [(set-var? st) st]
   [(empty-set? st) st]
   [else
    (let ([st-r (normalize (set-right st))])
      (cond
       [(set-var? st-r) st]
       [(empty-set? st-r) st]
       [else 
        (set (append (set-left st) (set-left st-r))
             (set-right st-r))]))]))

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
        [(or (empty-set? X) (empty-set? T)) #f]
        [(and (not (set? X)) (set? T))
         ((unify-well-formed-sets T X) a)]
        [(and (set? T)
              (same-set? (set-right X) (set-right T)))
         ((lazy-same X T) a)]
        [(and (set-var? T)
              (same-set? (set-right X) T))
         (let ([N (set-var (gensym 'n-unify))])
           ((update-s T (set (set-left X) N)) a))]
        [(set-var? T)
         ((update-s T X) a)]
        [(and (set? T) (set-member? X T)) #f]
        [(and (set? T) (not (same-set? (tail X) (tail T))))
         ((lazy-diff X T) a)]
        [else #f]))))

;; X = {t|s} = {t'|s'} = T
(define (lazy-diff X T)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((unify-well-formed-sets T (set-right X)) a)]
       [(null? (set-left T))
        ((unify-well-formed-sets X (set-right T)) a)]
       [else ((update-c (build-oc lazy-diff X T)) a)]))))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}
(define (lazy-same X T)
  (lambdam@ (a : s c)
    (let ([X (normalize (walk* X s))]
          [T (normalize (walk* T s))])
      (cond
       [(null? (set-left X))
        ((unify-well-formed-sets (set-right X) T) a)]
       [(and (set? T) (null? (set-left T)))
        ((unify-well-formed-sets (set-right T) X) a)]
       [else ((update-c (build-oc lazy-same X T)) a)]))))

;; X = {t|s} = {t'|s'} = T
(define (enforce-lazy-diff oc)
  (lambdag@ (a : s c)
    (let ([X (normalize (walk* (car (oc-rands oc)) s))]
          [T (normalize (walk* (cadr (oc-rands oc)) s))])
      (let ([t  (car (set-left X))]
            [s  (set (cdr (set-left X)) (set-right X))]
            [t^ (car (set-left T))]
            [s^ (set (cdr (set-left T)) (set-right T))]
            [n  (set-var (gensym 'n-diff))])
        ((conde
          ((== t t^) (== s s^))
          ((== t t^) (== (set `(,t) s) s^))
          ((== t t^) (== s (set `(,t^) s^)))
          ((== s (set `(,t^) n)) (== (set `(,t) n) s^)))
         a)))))

;; X = {t0 .. tm | M} 
;; T = {t'0 .. t'n | M}
(define (enforce-lazy-same oc)
  (lambdag@ (a : s c)
    (let ([X (normalize (walk* (car (oc-rands oc)) s))]
          [T (normalize (walk* (cadr (oc-rands oc)) s))]
          [N (set-var (gensym 'n-same))])
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
                ((== t0 tj)
                 (== (set (cdr ts) M) (set (rem1 tj t^s) M)))
                ((== t0 tj)
                 (== (set ts M) (set (rem1 tj t^s) M)))
                ((== t0 tj)
                 (== (set (cdr ts) M) (set t^s M)))
                ((== M (set `(,t0) N))
                 (== (set (cdr (set-left X)) N)
                     (set (set-left T) N)))
                ((loop (cdr tjs)))))]))
         a)))))

(define (same-set? s s^)
  (cond
   [(eq? s s^) #t]
   [(or (not (set? s))
        (not (set? s^)))
    #f]
   [(and (empty-set? s)
         (empty-set? s^))
    #t]
   [(and (equal? (set-left s) (set-left s^))
         (same-set? (set-right s) (set-right s^)))
    #t]
   [else #f]))

(define (tail s)
  (cond
   [(empty-set? s) s]
   [(set-var? s) s]
   [else (tail (set-right s))]))

(define (enforce-set-cs x)
  (lambdag@ (a)
    ((fresh ()
       (loop 'lazy-same enforce-lazy-same)
       (loop 'lazy-diff enforce-lazy-diff)
       (lambdag@ (a^ : s^ c^)
         (cond
          [(and (null? (filter/rator 'lazy-same c^))
                (null? (filter/rator 'lazy-diff c^)))
           a^]
          [else ((enforce-set-cs x) a^)])))
     a)))

(define (loop sym fn)
  (lambdag@ (a : s c)
    (let ([ocs (filter/rator sym c)]
          [rest (filter-not/rator sym c)])
      ((let inner ([ocs ocs])
         (cond
          [(null? ocs) 
           unitg]
          [else 
           (fresh () 
             (fn (car ocs))
             (inner (cdr ocs)))]))
       (make-a s rest)))))

(define (rem1 x ls)
  (cond
   [(null? ls) ls]
   [(eq? (car ls) x) (cdr ls)]
   [else (cons (car ls) (rem1 x (cdr ls)))]))

(define (make-set ls)
  (if (null? ls)
      (empty-set)
      (set ls (empty-set))))

(define (seto u) (goal-construct (well-formed-set-c u)))

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

(extend-enforce-fns 'sets enforce-set-cs)

(module+ test
  (test "test 0.0" (run* (q) (== 5 5)) '(_.0))
  (test "test 0.1" (run* (q) (== 5 6)) '())
  (test "test 0.2" (run* (q) (fresh (x) (== q `(,x)))) '((_.0)))
  (test "test 0.3" (run* (q) (=/= 5 6)) '(_.0))

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

  (test "test 6"
        (run* (q) (== q (make-set '(1 2))))
        '((set (1 2))))

  (test "test 7"
        (run* (q) 
          (== q (make-set '(1)))
          (== q (make-set '(2))))
        '())
  
  (test "test 8.0"
        (run* (q) (== q (set '(1) q)))
        `((set (1 s.0))))

  (test "test 8.1"
        (run* (q) (== (set '(1) q) q))
        `((set (1 s.0))))

  (test "test 9.0"
        (run* (q) (fresh (z) (== q (set `(,z) q))))
        '((set (_.0 s.1))))

  (test "test 9.1"
        (run* (q) (fresh (z) (== q (set '(1) z))))
        '((set (1 s.0))))

  (test "test 9.2"
        (run* (q) (fresh (z) (== q (set `(,(set '(1) z)) q))))
        '((set ((set (1 s.0)) s.1))))

  (test "test 9.5"
        (run* (q) 
          (== (set `(1) q) (set `(2) (empty-set))))
        '())

  (test "enforce-lazy-same"
        (run* (q)
          (seto q)
          (enforce-lazy-same (build-oc lazy-same (set `(1) q) (set `(2) q))))
        '((set (1 2 s.0))))

  (test "test 10.0"
        (run* (q) 
          (== (set `(1) q) (set `(2) q)))
        '((set (1 2 s.0))))

  (test "test 10.1"
        (run* (q) 
          (fresh (x y r s) 
            (== (set `(1) r) (set `(2) s))))
        '(_.0))

  ;; Wrong, yes
  (test "test 10.05"
        (run 1 (q) 
          (fresh (x y r)
            (== (set `(,x) r) (set `(,y) r))))
        '(_.0))
  
  (test "test 10.06"
        (run* (q)
          (== q (set '() (set '(1) q))))
        '((set (1 s.0))))

  (test "test 10.07"
        (run* (q)
          (== (set '() q) (set '() q)))
        '(s.0))

  ;; Wrong?
  (test "test 10.08" 
        (run* (q)
          (== q (set '() q)))
        '(s.0))

  (test "test 10.09"
        (run* (q)
          (== (set '() (set '() q)) (set '() q)))
        '(s.0))

  (test "test 10.1"
        (run* (q)
          (fresh (y r s)
            (== q y)
            (== (set `(,q) r) (set `(,y) s))))
        '(_.0 _.0 _.0 _.0))

  (test "test 9.iv.1"
        (run* (q)
          (== (set `(1) (set `(2) (empty-set)))
              (set `(2) (set `(1) (empty-set)))))
        `(_.0))

  (test "test 10.3"
        (run* (q) 
          (fresh (y r s) 
            (== (set `(,q) r) (set `(,y) s))))
        '(_.0 _.0 _.0 _.0))

  (test "test 10.2"
        (run* (q) 
          (fresh (x y r s) 
            (== q `(,x ,r ,y ,s))
            (== (set `(,x) r) (set `(,y) s))))
        '((_.0 s.1 _.0 s.1)
          (_.0 s.1 _.0 (set (_.0 s.1)))
          (_.0 (set (_.0 s.1)) _.0 s.1)
          (_.0 (set (_.1 s.2)) _.1 (set (_.0 s.2)))))
)

