#lang racket

(require 
 cKanren/src/framework
 cKanren/src/constraints
 cKanren/src/variables
 cKanren/src/package
 cKanren/src/infs
 cKanren/src/events
 cKanren/src/operators
 cKanren/src/running
 cKanren/src/triggers
 cKanren/src/macros
 cKanren/src/substitution
 racket/generator
 "../tester.rkt")

(define u (var 'u))

(let ()
  (define test-event
    (build-chain-event
     (add-association-event u 'a)
     (empty-event)
     (add-substitution-prefix-event '())
     (composite-event
      (list (add-substitution-prefix-event `((,u . b)))))))
  (test (walk u '() #f test-event) 'a))

(let ()
  (define test-event
    (build-chain-event
     (add-substitution-prefix-event `((,u . a)))
     (empty-event)
     (add-substitution-prefix-event '())
     (composite-event
      (list (add-substitution-prefix-event `((,u . b)))))))
  (test (walk u '() #f test-event) 'a))

(let ()
  (define test-event
    (build-chain-event
     (add-substitution-prefix-event `())
     (empty-event)
     (add-substitution-prefix-event '())
     (composite-event
      (list (add-substitution-prefix-event `((,u . b)))))))
  (test (walk u '() #f test-event) 'b))

(let ()
  (define a-inf (bindm empty-a (conj succeed succeed)))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list empty-a)))

(let ()
  (define a-inf (bindm empty-a (conj succeed (enforce (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list empty-a)))

(let ()
  (define a-inf (bindm empty-a (conj succeed (enforce (var 'x)) (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list '_.0)))

(test
 (run 1 (q) succeed)
 '(_.0))

(test
 (run 1 (q) fail)
 '())

(test
 (run 1 (q) (conde [fail] [fail]))
 '())

(test
 (run 1 (q) (conde [succeed] [fail]))
 '(_.0))

(test
 (run* (q) (conde [succeed] [fail]))
 '(_.0))

(test
 (run 1 (q) (add-association q 5))
 '(5))

(test
 (run* (q) (add-association q 5))
 '(5))

(define-constraint (reifiedc x)
  #:reified)

(test
 (run 1 (q) (add-constraint (reifiedc q)))
 '((_.0 : (reifiedc _.0))))

(test
 (run* (q) (add-constraint (reifiedc q)))
 '((_.0 : (reifiedc _.0))))

(define (check-store-empty rator)
  (lambda@ (a [s c q t e])
    (cond
     [(null? (filter/rator rator c)) a]
     [else (error 'test "constraint store not empty when it shouldn't be: ~a\n" c)])))

(define (check-store-not-empty rator)
  (lambda@ (a [s c q t e])
    (cond
     [(null? (filter/rator rator c)) 
      (error 'test "constraint store empty when it shouldn't be: ~a\n" c)]
     [else a])))

(let ()
  (define-constraint (exc x)
    #:reified
    (cond
     [(not (var? x)) succeed]
     [else (add-constraint (exc x))]))

  (test
   (run* (q) (add-association q 5) (exc q))
   '(5))

  (test
   (run* (q) 
     (exc q) 
     (add-association q 5)
     (check-store-empty exc))
   '(5)))

(let ()
  (define-trigger (extr rator)
    [(add-constraint-event ra rn)
     (=> abort)
     (unless (eq? ra rator) (abort))])

  (define-constraint (exc1 x)
    #:reaction
    [(extr reifiedc)
     (add-constraint (exc2 x))])

  (define-constraint (exc2 x) #:reified)

  (test
   (run* (q)
     (exc1 q)
     (reifiedc q)
     (check-store-empty exc1))
   '((_.0 : (exc2 _.0) (reifiedc _.0))))

  (define-trigger (true-immediately)
    [(empty-event) #t])

  (define-constraint (exc3 x)
    #:reaction
    [(true-immediately)
     (add-constraint (exc2 x))])

  ;; checks reactions that fire when you first enter the body of the
  ;; constraint (i.e. before the constraint is coming from the store)
  (test
   (run* (q) 
     (exc3 q)
     (check-store-empty exc3))
   '((_.0 : (exc2 _.0)))))

(define-trigger (rem-tr rator)
  [(remove-constraint-event/internal rator^ rands^)
   (=> abort)
   (unless (eq? rator rator^) (abort))])

(define-trigger (add-tr rator)
  [(add-constraint-event/internal rator^ rands^)
   (=> abort)
   (unless (eq? rator rator^) (abort))])

(define-constraint (rem-self x)
  #:reaction
  [(rem-tr rem-self)
   (error 'test "should not see itself removed")])

(define-constraint (add-self x)
  #:reaction
  [(add-tr add-self)
   (error 'test "should not see itself added")])

(test
 (run* (q)
   (let ([rator rem-self]
         [rands (list q)])
     (conj (add-constraint (oc rator rands))
           (remove-constraint (oc rator rands)))))
 '(_.0))

(test
 (run* (q)
   (let ([rator add-self]
         [rands (list q)])
     (conj (add-constraint (oc rator rands))
           (remove-constraint (oc rator rands)))))
 '(_.0))

(define-constraint (exc8 x)
  #:reaction
  [(add-tr rem-self)
   (add-constraint (reifiedc x))]
  #:reaction
  [(add-tr add-self)
   (conj (add-constraint (reifiedc x))
         (exc8 x))])

(test
 (run* (q)
   (exc8 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal add-self (list q))
           (add-constraint-event/internal rem-self (list q)))))
   (check-store-empty exc8))
 '((_.0 : (reifiedc _.0))))

(test
 (run* (q)
   (exc8 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal rem-self (list q))
           (add-constraint-event/internal add-self (list q)))))
   (check-store-empty exc8))
 '((_.0 : (reifiedc _.0))))

(define-constraint (exc9 x)
  #:reaction
  [(add-tr rem-self)
   (conj (add-constraint (reifiedc x))
         (add-constraint (exc9 x)))]
  #:reaction
  [(add-tr add-self)
   (conj (add-constraint (reifiedc x))
         (add-constraint (exc9 x)))])

(test
 (run* (q)
   (exc9 q)
   (send-event (add-constraint-event/internal rem-self (list q))))
 '((_.0 : (reifiedc _.0))))

(test
 (run* (q)
   (exc9 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal rem-self (list q))
           (add-constraint-event/internal add-self (list q))))))
 '((_.0 : (reifiedc _.0 _.0))))

;; (chain exc12 exc11)
;; (chain exc13 ...)

(let ()
  (define-constraint (exc10 x y)
    #:reified
    #:reaction
    [(add-tr exc15)
     (add-constraint (exc10 x 5))])

  (define-constraint (exc11 x)
    #:reaction
    [(add-tr exc12)
     (add-constraint (exc15 x))])

  ;; dummies
  (define-constraint (exc12 x))
  (define-constraint (exc13 x))

  (define-constraint (exc14 x)
    #:reaction
    [(add-tr exc13)
     (exc10 x x)])

  (define-constraint (exc15 x))

  ;; can running events (on the left side of a running-event) properly
  ;; communicate their existance to each other?
  (test
   (run* (q)
     (send-event 
      (composite-event
       (list (add-constraint-event/internal exc15 (list q))
             (add-constraint-event/internal exc10 (list q q))))))
   '((_.0 : (exc10 (_.0 5)))))

  ;; can the same happen with one level of indirection?
  (test
   (run* (q)
     (exc11 q)
     (exc14 q)
     (send-event 
      (composite-event
       (list (add-constraint-event/internal exc12 (list q))
             (add-constraint-event/internal exc13 (list q))))))
   '((_.0 : (exc10 (_.0 5))))))

(define-trigger (sneaky a-rator)
  [(add-constraint-event/internal rator rands)
   (=> abort)
   ;; this has to be cons (atm) because we have a list in the
   ;; constraint-interaction user interface with unquotes.
   ;; TODO: get rid of the unquotes.
   (unless (eq? rator a-rator)
     (abort))
   (remove-constraint (oc rator rands))])

(let ()

  (define-constraint (exc16 q)
    #:reaction
    [(sneaky exc17)
     => (lambda (response) response)])

  (define-constraint (exc17 q))

  (test
   (run* (q)
     (add-constraint (exc16 q))
     (exc17 q)
     (check-store-empty exc17))
   '(_.0)))

(let ()
  
  (define-constraint (exc16 q)
    #:reaction
    [(sneaky exc17)
     => (lambda (response) response)])

  (define-constraint (exc17 q))
  
  (define-constraint (exc18 q)
    #:reaction
    [(add-tr exc17)
     (conj (add-constraint (exc18 q))
           (add-constraint (reifiedc q)))])

  (test
   (run* (q)
     (exc16 q)
     (exc18 q)
     (exc17 q))
   '(_.0)))

(let ()
  (test (exit/ir (start/ir)) '(_.0)))

(let ()
  (test (exit/ir (extend/ir (start/ir) #:var q (add-association q 5))) '(5)))

(let ()
  (define-constraint (ex x)
    #:reify 5)
  (test (run* (q) (ex q)) '((_.0 : (ex 5)))))

(let ()
  (define-constraint (foo x y) #:reified)

  (define-constraint (fooi an-oc) 
    #:reaction
    [(removed-constraint (if an-oc (list an-oc) (list)))
     (fooi #f)]
    #:reaction
    [(added-constraint
      (lambda (an-oc^) 
        (cond
         [an-oc
          (and (eq? (car an-oc^) foo)
               (not (= (cadr an-oc) (cadr an-oc^)))
               an-oc^)]
         [else (and (eq? (car an-oc^) foo) an-oc^)])))
     =>
     (lambda (an-oc^)
       (cond
        [an-oc
         (conj
          (remove-constraint (oc (car an-oc) (cdr an-oc)))
          (remove-constraint (oc (car an-oc^) (cdr an-oc^)))
          (add-constraint (foo (+ (cadr an-oc) (cadr an-oc^)) (caddr an-oc))))]
        [else (fooi an-oc^)]))]
    #:reify 
    (if an-oc (cons 'foo (cdr an-oc)) #f))

  (test (run* (q) (foo 5 q)) '((_.0 : (foo (5 _.0)))))
  (test (run* (q) (fooi #f) (foo 5 q)) 
        '((_.0 : (foo (5 _.0)) (fooi (foo 5 _.0)))))
  (test (run* (q) (fooi #f) (foo 5 q) (foo 6 q)) 
        '((_.0 : (foo (11 _.0)))))

  (test (run* (q) 
          (fooi #f)
          (send-event
           (composite-event
            (list (add-constraint-event/internal foo (list 5 q))
                  (add-constraint-event/internal foo (list 6 q))))))
        '((_.0 : (foo (11 _.0)))))
  
  (test (run* (q) 
          (send-event
           (composite-event
            (list 
             (add-constraint-event/internal fooi (list #f))
             (add-constraint-event/internal foo (list 5 q))
             (add-constraint-event/internal foo (list 6 q))))))
        '((_.0 : (foo (11 _.0)))))
  
  (test (run* (q) 
          (send-event
           (composite-event
            (list 
             (add-constraint-event/internal fooi (list (cons foo (list 5 q))))
             (remove-constraint-event/internal foo (list 5 q)))))
          (check-store-not-empty fooi))
        '(_.0))

  (test (run* (q) 
          (send-event
           (composite-event
            (list 
             (add-constraint-event/internal fooi (list (cons foo (list 5 q))))
             (remove-constraint-event/internal foo (list 5 q))
             (add-constraint-event/internal foo (list 6 q))))))
        '((_.0 : (foo (6 _.0)) (fooi (foo 6 _.0)))))
  )
