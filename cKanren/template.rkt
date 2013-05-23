#lang racket

(require "ck.rkt" "tree-unify.rkt")

(provide templateo)

;; goal that will copy the "template" in t, i.e. the structure and
;; free variables, to x
(define (templateo t x)
  (goal-construct (init-template t x)))

(define empty-env '())
(define (extend-env x v env) (cons `(,x . ,v) env))
(define (lookup-env x env)
  (cond
   [(assq x env) => cdr]
   [else #f]))

(define (make-var x env)
  (cond
   [(not (var? x))
    (values (var 'new-pair) env)]
   [(lookup-env x env)
    => (lambda (x^) (values x^ env))]
   [else 
    (define x^ (var 'new-var))
    (values x^ (extend-env x x^ env))]))

(define (init-template t x)
  (let ([new-env-var (var 'env)])
    (composem
     (template-env new-env-var empty-env)
     (template t x new-env-var))))

;; if t is an mk-struct, copies that structure onto x.  if t is ground
;; or if there is already a (template x t) constraint, this constraint
;; turns into ==. otherwise, placed back in the store.
(define (template t x env-var)
  (lambdam@ (a : s c)
    (let ([t (walk t s)]
          [x (walk x s)]
          [env (get-env env-var c)])
      (cond
       [(eq? t x) a]
       [(occurs-check x t s) #f]
       [(pair? t)
        (define-values (first env^) 
          (make-var (car t) env))
        (define-values (rest env^^)
          (make-var (cdr t) env^))
        (bindm a
          (composem
           (update-env env-var env^^)
           (==-c x `(,first . ,rest))
           (template (car t) first env-var)
           (template (cdr t) rest env-var)))]
       [(not (var? t))
        (bindm a (==-c t x))]
       [else (bindm a (update-c (build-oc template t x env-var)))]))))

(define (get-env env-var c)
  (let ([envs (filter/rator 'template-env c)])
    (cadr (oc-rands (findf (lambda (oc) (eq? (car (oc-rands oc)) env-var)) envs)))))

(define (update-env env-var env^)
  (lambdam@ (a : s c)
    ((update-c (build-oc update-env env-var env^)) a)))

(define (template-env env-var env)
  (lambdam@ (a : s c)
    (let ([env (walk* env s)])
      ((update-c (build-oc template-env env-var env)) a))))

(define-constraint-interaction
  update-env-trigger
  [(update-env ,env-var ,env^) (template-env ,env-var ,env)]
  [#t ((template-env env-var env^))])

(define-constraint-interaction
  template-to-unify
  [(template ,t ,x ,env1) (template ,x ,t ,env2)]
  [#t ((==-c t x))])

(define (specific-templateo t x)
  (conj (specifico t) (templateo t x)))

(define (specifico t)
  (goal-construct (specific t)))

(define (specific t)
  (lambdam@ (a : s c)
    (let ([t (walk t s)])
      ((update-c (build-oc specific t)) a))))

(define (enforce-specifics x)
  (lambdag@ (a : s c)
    ((let loop ([specs (filter/rator 'specific c)])
       (cond
        [(null? specs) succeed]
        [else 
         (conj 
          (make-specifico (car (oc-rands (car specs))))
          (loop (cdr specs)))]))
     a)))

(define (make-specifico spec)
  (goal-construct (make-specific spec)))

(define (make-specific t)
  (lambdam@ (a : s c)
    (let ([ts (filter (lambda (oc) (eq? (car (oc-rands oc)) t))
                      (filter/rator 'template c))])
      (cond
       [(null? ts) a]
       [else
        (let ([specific-pattern
               (for/fold 
                ([specific-pattern (cadr (oc-rands (car ts)))])
                ([pat (cdr ts)])
                (union-pattern specific-pattern (cadr (oc-rands pat)) s c))])
          (bindm a (==-c t specific-pattern)))]))))

(define (union-pattern spec pat s c)
  (cond
   ;; check to see if spec and pat already unify.. if they do we don't
   ;; have to change anything in spec
   [(unify `((,spec . ,pat)) s c)
    => (lambda (s/c) spec)]
   ;; if they are compatible but do not unify, we have to figure out
   ;; which sub-expressions fail to unify and replace those with fresh
   ;; variables
   [(and (unifiable? spec)
         (unifiable? pat)
         (compatible? spec pat s c)
         (compatible? pat spec s c))
    (gen-anti-unify spec pat s c)]
   ;; if they are unifiable but not compatible, or just not unifiable,
   ;; return the most general answer
   [else (var (gensym 'union-fail))]))

(define (gen-anti-unify spec pat s c)
  (cond
   [(and (mk-struct? spec)
         (mk-struct? pat))
    (recur spec
           (lambda (ua ud)
             (recur pat
                    (lambda (va vd)
                      ((constructor spec)
                       (union-pattern ua va s c)
                       (union-pattern ud vd s c))))))]
   [else (var (gensym 'gen-fail))]))

(extend-enforce-fns 'specifics enforce-specifics)

(module+ test
  (require "tester.rkt")
  (test "0" (run* (q) (templateo 5 5)) '(_.0))
  (test "1" (run* (q) (templateo q q)) '(_.0))
  (test "2" (run* (q) (templateo 5 q)) '(5))
  (test "3" (run* (q) (templateo q 5) (templateo q 6)) '(_.0))
  (test "4" 
        (run* (q) 
          (fresh (x y)
            (templateo q 5)
            (== `(,x ,y) q)))
        '())
  (test "5"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '((_.0 . _.1)))
  (test "6"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q 5)))
        '())
  (test "7"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4))))
        '(_.0))

  #;
  (test "8"
        (run* (q)
          (fresh (x y z)
            (templateo x y)
            (templateo y z)
            (templateo z x)
            (== q `(,x ,y ,z))))
        '((_.0 _.0 _.0)))


  (test "9" (run* (q) (templateo `(,q) q)) '())

  (test "10"
        (run* (q) (fresh (x y) (templateo `(,x ,x) y) (== q `(,x ,y))))
        '((_.0 (_.1 _.1))))

  (test "11"
        (run* (q) (fresh (x y) (templateo `((,x) (,x)) y) (== q `(,x ,y))))
        '((_.0 ((_.1) (_.1)))))

  (test "12"
        (run 1 (q) (fresh (x y) (templateo `(lambda (,x) (,y ,x)) q)))
        '((lambda (_.0) (_.1 _.0))))
)


