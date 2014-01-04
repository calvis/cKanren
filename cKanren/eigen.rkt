#lang racket

(require "src/base.rkt" "tree-unify.rkt"
         "attributes.rkt" "neq.rkt" "src/mk-structs.rkt"
         "src/framework.rkt" "src/triggers.rkt")
(require "tester.rkt")

;; a "fresh" for EigenVars
(provide eigen)

;; an EigenVar is just a special kind of Var
(define-var-type eigenvar "ev"
  #:methods gen:unifiable
  [(define (compatible? ev v s c e)
     (and (var? v) (in-scope? ev v c e)))
   (define (gen-unify ev v p s c e)
     (unify p (ext-s v ev s) c e))])

;; a macro for introducing new EigenVars
(define-syntax-rule (eigen (x ...) g ...)
  (fresh-aux eigenvar (x ...)
    (track-eigen x '()) ...
    (conj g ...)
    (leave-eigen x) ...))

;; EigenVar [List-of Var] -> ConstraintTransformer
;; fails when x is involved in unification of variables not in scope
(define-constraint (track-eigen x [in-scope update-scope])
  ;; track any change in scope by responding to #f
  #:reaction
  [(enter-scope #f)
   => (lambda (y) (add-constraint (track-eigen x (cons y in-scope))))]
  #:reaction
  [(leave-scope #f)
   => (lambda (y) (add-constraint (track-eigen x (remq y in-scope))))]

  ;; track associations to x
  #:reaction
  [(any-association-event x) 
   => (lambda (p)
        (conj (add-constraint (track-eigen x in-scope))
              (check-associations x p in-scope)))])

;; [List-of Value] -> [List-of Var]
;; updates the EigenVar scope list
(define (update-scope x . rest)
  (filter*/var? (apply walk x rest)))

;; EigenVar SubstitutionPrefix [List-of Var] -> ConstraintTransformer
;; the prefix is a list of either (x . something) or (somevar . x)
(define (check-associations x prefix in-scope)
  (transformer
   #:package (a [s c e])
   (if (andmap (prefix-okay? x s in-scope) prefix) succeed fail)))

(define (prefix-okay? x s in-scope)
  (match-lambda 
    [(cons u v)
     (cond
      ;; a binding (x . something)
      [(and (eq? u x) (not (eq? v x))) #f]
      ;; a binding (somevar . x)
      [(memq u in-scope)
       (define p^ 
         (filter (lambda (p) (memq u (filter*/var? (cdr p)))) s))
       (andmap (curryr memq in-scope) p^)]
      [else #f])]))

;; TODO: this should just be #:persistent
(define-constraint (leave-eigen x)
  (add-constraint (leave-eigen x)))

;; when you leave scope, get rid of both constraints
(define-constraint-interaction
  [(track-eigen x ls) (leave-eigen x)] => [succeed])

;; if you try to unify a symbol/number with an EigenVar, fails
(define-constraint-interaction
  [(track-eigen x ls) (symbol x)] => [fail])
(define-constraint-interaction
  [(track-eigen x ls) (number x)] => [fail])

;; EigenVar Var ConstraintStore Event -> Boolean
;; returns #t iff it is okay to unify ev and v based on ev's scope
;; TODO: should check event
(define (in-scope? ev v c e)
  (define eigen-rands
    (filter/rator track-eigen c))
  (define the-rands 
    (findf (lambda (rands) (eq? (car rands) ev))
           eigen-rands))
  (memq v (cadr the-rands)))

;; Test the eigen variable implementation in miniKanren

(module+ test
  ;; there exists q st. forall x, x = q
  (test (run* (q) (eigen (x) (== x q))) '())

  ;; forall x, there exists y st. x = y
  (test (run* (q) (eigen (x) (fresh (y) (== x y)))) '(_.0))

  (test (run* (q) (eigen (x) (fresh (y) (== x y) (== q y)))) '())
  (test (run* (q) (eigen (x) (fresh (y) (== x y) (== y q)))) '())

  (test (run* (q) (eigen (x) (symbol x))) '())

  (test (run* (q) (eigen (x) (number x))) '())

  (test (run* (q) (eigen (e) (fresh (x) (number x) (== x e)))) '())

  (test (run* (q) (eigen (e) (fresh (x) (== x e) (number x)))) '())

  (test (run* (q) (eigen (e) (fresh (x) (== x e)))) '(_.0))

  (test (run* (q) (eigen (e) (symbol e))) '())

  (test (run* (q) (eigen (e1) (== e1 5))) '())

  (test (run* (q) (eigen (e1 e2) (== e1 e2))) '())

  (test
   (run* (q)
     (eigen (e1)
       (fresh (x y)
         (== e1 `(,x . ,y)))))
   '())

  (test (run* (q) (eigen (x) (== q x))) '())

  (test (run* (q) (eigen (x) (fresh (r) (== r x)))) '(_.0))

  (test (run* (q) (eigen (a) (fresh (x) (== `(1 2 3 ,x 4) a))))
        '())

  (test (run* (q) (fresh (x) (eigen (a) (== `(1 2 3 ,x 4) a))))
        '())

  ;; HARD
  (test
   (run* (q) 
     (eigen (x) 
       (fresh (y) 
         (== `(,x) y)
         (== y q))))
   '())

  (test (run* (q) (eigen (e) (fresh (y) (== `(,y) q) (== y e)))) '())

  (test (run* (q) (eigen (e) (fresh (y) (== y e) (== `(,y) q)))) '())

  ;; there exists x st. forall a, `(1 2 3 ,a 4) is x
  (test (run* (q) (fresh (x) (eigen (a) (== `(1 2 3 ,a 4) x))))
        '())

  ;; forall e, there exists a list `(1 2 3 ,e 4)
  (test (run* (q) (eigen (e) (fresh (x) (== `(1 2 3 ,e 4) x))))
        '(_.0))


  (test (run* (q) (eigen (e1) (eigen (e2) (fresh (x y) (== x e1) (== y e2) (== x y)))))
        '())

  (test
   (run* (q) (eigen (e1) (eigen (e2) (fresh (x y) (== x y) (== x e1) (== y e2)))))
   '())

  (test
   (run* (q) (eigen (e1) (eigen (e2) (fresh (x y) (== x e1) (== x y) (== y e2)))))
   '())

  (test
   (run* (q)
     (eigen (e e2)
       (fresh (x)
         (== `(,x . ,x) `(,e . ,e2)))))
   '())

  (test
   (run* (q)
     (eigen (e)
       (fresh (x)
         (== `(,e . ,q) `(,x . ,x)))))
   '())

  ;; Tests below this point fail.

  #;
  (test "eigen test 9"
  (run 1 (q) (eigen (x) (absento x q)))
  '(_.0))

  ;; there exists q st. forall x, x != q
  (test (run* (q) (eigen (x) (=/= x q))) '())

  (test (run* (q) (eigen (e) (=/= 5 e))) '())

  (test (run* (q) (eigen (e1 e2) (=/= e1 e2))) '())

  (test "eigen-=/=-1"
        ;; exists Q . forall E . Q =/= E
        ;; false (pick E = Q)
        (run 1 (q) (eigen (e) (=/= q e)))
        '())

  (test "eigen-=/=-2"
        ;; forall E . exists X . E =/= X
        ;; true (pick X =/= E)
        (run 1 (q) (eigen (e) (fresh (x) (=/= e x))))
        '(_.0))

  (test "eigen-=/=-3a"
        ;; forall E1 E2 . E1 =/= E2
        ;; false (pick E1 = E2)  
        (run 1 (q) (eigen (e1 e2) (=/= e1 e2)))
        '())

  (test "eigen-=/=-3b"
        ;; forall E1 . forall E2 . E1 =/= E2
        ;; false (pick E2 = E1)  
        (run 1 (q) (eigen (e1) (eigen (e2) (=/= e1 e2))))
        '())

  (test "eigen-=/=-4"
        ;; forall E1 . E1 =/= E1
        ;; false (pick any legal term for E1)  
        (run 1 (q) (eigen (e1) (=/= e1 e1)))
        '())

  (test "eigen-=/=-5"
        ;; forall E1 . E1 =/= 5
        ;; false (pick E1 = 5) 
        (run 1 (q) (eigen (e1) (=/= e1 5)))
        '())

  (test "eigen-=/=-list-1"
        ;; forall A . exists X . `(1 2 3 ,A 4) =/= X
        ;; true (pick X to be any non-list value, for example)  
        (run 1 (q) (eigen (a) (fresh (x) (=/= `(1 2 3 ,a 4) x))))
        '(_.0))

  (test "eigen-=/=-list-2"
        ;; forall A . exists X . `(1 2 3 ,X 4) =/= A
        ;; true (if A is `(1 2 3 ,Y 4), choose X =/= Y)
        (run 1 (q) (eigen (a) (fresh (x) (=/= `(1 2 3 ,x 4) a))))
        '(_.0))

  (test "eigen-=/=-list-3"
        ;; exists X . forall A . `(1 2 3 ,A 4) =/= X
        ;; true (pick X to be any non-list value, for example)  
        (run 1 (q) (fresh (x) (eigen (a) (=/= `(1 2 3 ,a 4) x))))
        '(_.0))

  (test "eigen-=/=-list-4"
        ;; exists X . forall A . `(1 2 3 ,X 4) =/= A
        ;; false (if X is any legal term, choose A = `(1 2 3 ,X 4))  
        (run 1 (q) (fresh (x) (eigen (a) (=/= `(1 2 3 ,x 4) a))))
        '())
  )
