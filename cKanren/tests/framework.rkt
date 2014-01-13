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
 cKanren/src/mk-structs
 racket/generator
 "../tester.rkt")

(define u (var 'u))
(define rator1 (lambda (x) x))
(define rands1 (list 5))
(define rands1-equal (list 5))
(define rator2 (lambda (x) x))
(define rands2 (list 6))

;; == EVENT TESTS ==============================================================

(test
 (compose-events
  (constraint-event rator1 rands1)
  (running-event (add-substitution-prefix-event `((q . 5))) (empty-event)))
 (running-event
  (add-substitution-prefix-event `((q . 5)))
  (constraint-event rator1 rands1)))

(test
 (compose-events
  (add-substitution-prefix-event `((x . 5)))
  (add-substitution-prefix-event `((x . 5))))
 (add-substitution-prefix-event `((x . 5) (x . 5))))

(test
 (compose-events
  (composite-event
   (list (add-substitution-prefix-event `((x . 5)))))
  (add-substitution-prefix-event `((x . 5))))
 (add-substitution-prefix-event `((x . 5) (x . 5))))

(test
 (<e (empty-event)
     (running-event (empty-event) (empty-event)))
 #t)

(test
 (<e (composite-event (list (empty-event) (empty-event)))
     (running-event (empty-event) (empty-event)))
 #t)

(test 
 (pessimistic-merge (empty-event) (empty-event))
 (empty-event))

(test 
 (compose-events
  (add-constraint-event/internal rator1 rands1-equal)
  (build-chain-event 
   (empty-event)
   (empty-event)
   (empty-event)
   (remove-constraint-event/internal rator1 rands1)))
 (build-chain-event (empty-event) (empty-event) (empty-event) (empty-event)))

(test
 (compose-events
  (add-constraint-event/internal rator1 rands1)
  (build-chain-event
   (add-constraint-event/internal rator2 rands2)
   (empty-event)
   (add-constraint-event/internal rator2 rands2)
   (composite-event
    (list
     (add-constraint-event/internal rator1 rands2)
     (remove-constraint-event/internal rator1 rands1)))))
 (build-chain-event
  (add-constraint-event/internal rator2 rands2)
  (empty-event)
  (add-constraint-event/internal rator2 rands2)
  (add-constraint-event/internal rator1 rands2)))

(test
 (findf 
  association-event?
  (running-event
   (add-substitution-prefix-event '())
   (empty-event)))
 (add-substitution-prefix-event '()))

(test
 (findf
  (curry relevant? u)
  (build-chain-event
   (add-substitution-prefix-event `((,u . 1)))
   (add-substitution-prefix-event `())
   (add-substitution-prefix-event `((,u . 2)))
   (composite-event
    (list
     (add-substitution-prefix-event `((,u . 3)))
     (remove-constraint-event/internal rator1 rands1)))))
 (add-substitution-prefix-event `((,u . 1))))

(test
 (findf
  (curry relevant? u)
  (build-chain-event
   (add-substitution-prefix-event '())
   (add-substitution-prefix-event '())
   (empty-event)
   (composite-event
    (list
     (add-substitution-prefix-event `((,u . a)))
     (remove-constraint-event/internal rator1 rands1)))))
 (add-substitution-prefix-event `((,u . a))))

(let ([ce (add-substitution-prefix-event '())])
  (test
   (findf
    (curry relevant? u)
    (build-chain-event
     ce
     (chain-event 
      ce
      (add-substitution-prefix-event `((,u . a))))
     ce
     (empty-event)))
   (add-substitution-prefix-event `((,u . a)))))

(let ([ce (add-substitution-prefix-event '())])
  (test
   (findf
    (curry relevant? u)
    (build-chain-event
     (empty-event)
     (chain-event 
      ce
      (add-substitution-prefix-event `((,u . a))))
     ce
     (empty-event)))
   (add-substitution-prefix-event `((,u . a)))))

(let ([ce (add-substitution-prefix-event '((g t)))])
  (test
   (findf
    (curry relevant? u)
    (build-chain-event 
     ce
     (chain-event ce 
                  (composite-event 
                   (list 
                    (add-substitution-prefix-event `((r)))
                    (constraint-event (lambda (x) x) `(t f g))
                    (add-substitution-prefix-event `((,u f . r)))
                    (constraint-event (lambda (x) x) `(g ,u g)))))
     ce
     (constraint-event (lambda (x) x) `(g ,u))))
   (add-substitution-prefix-event `((,u f . r)))))

(let ([ce (add-substitution-prefix-event '((g t)))])
  (test
   (findf
    (curry relevant? u)
    (build-chain-event 
     ce
     (chain-event ce 
                  (composite-event 
                   (list 
                    (leave-scope-event 'r)
                    (leave-scope-event 'f)
                    (add-substitution-prefix-event `((r)))
                    (constraint-event (lambda (x) x) `(t f g))
                    (add-substitution-prefix-event `((,u f . r)))
                    (enter-scope-event 'r)
                    (enter-scope-event 'f)
                    (constraint-event (lambda (x) x) `(g f g)))))
     ce
     (constraint-event (lambda (x) x) `(g ,u))))
   (add-substitution-prefix-event `((,u f . r)))))

(test
 (compose-events
  (build-chain-event
   (add-substitution-prefix-event `((q . 5)))
   (add-substitution-prefix-event `((q . 5)))
   (add-substitution-prefix-event `((q . 5)))
   (empty-event))
  (constraint-event rator1 rands1))
 (build-chain-event
  (add-substitution-prefix-event `((q . 5)))
  (add-substitution-prefix-event `((q . 5)))
  (add-substitution-prefix-event `((q . 5)))
  (constraint-event rator1 rands1)))

(let ([trigger (add-substitution-prefix-event `((q . 5)))])
  (test
   (apply-chain
    (build-chain-event
     trigger
     (empty-event)
     trigger
     (composite-event
      (list
       (constraint-event rator1 rands2)
       (constraint-event rator1 rands1)))))
   (running-event
    trigger
    (chain-event
     trigger
     (composite-event
      (list
       (constraint-event rator1 rands2)
       (constraint-event rator1 rands1)))))))

(let ([tr (add-substitution-prefix-event `((q . 5)))])
  (test
   (solidify
    (list tr)
    (chain-event tr (add-substitution-prefix-event `((q . 6)))))
   (add-substitution-prefix-event `((q . 6)))))

(let ([trigger1 (add-substitution-prefix-event `((q . 5)))]
      [trigger2 (add-constraint-event/internal rator1 rands1)])
  (test
   (solidify
    (list trigger1 trigger2)
    (composite-event
     (list (chain-event trigger1 (add-substitution-prefix-event `((q . 6))))
           (chain-event trigger2 (chain-event trigger1 (add-substitution-prefix-event `((q . 7))))))))
   (add-substitution-prefix-event `((q . 7) (q . 6)))))

;; == WALK TESTS ===============================================================

(let ()
  (define test-event
    (build-chain-event
     (add-substitution-prefix-event `((,u . a)))
     (empty-event)
     (add-substitution-prefix-event '())
     (composite-event
      (list (add-substitution-prefix-event `((,u . b)))))))
  (test (walk u '() #f test-event) 'a))

(let ([x (var 'x)])
  (define test-event
    (build-chain-event
     (composite-event
      (list (add-substitution-prefix-event `((,u . ,x)))
            (add-substitution-prefix-event `((,x . 5)))))
     (empty-event)
     (empty-event)
     (empty-event)))
  (test (walk u '() #f test-event) 5))

(let ([x (var 'x)])
  (define test-event
    (build-chain-event
     (composite-event
      (list (add-substitution-prefix-event `((,u . ,x)))
            (add-substitution-prefix-event `((,x . 5)))))
     (empty-event)
     (empty-event)
     (empty-event)))
  (test (walk x '() #f test-event) 5))

(let ([x (var 'x)])
  (define test-event
    (build-chain-event
     (composite-event
      (list (add-substitution-prefix-event `((r) (,u . ,x)))
            (add-substitution-prefix-event `((r) (,x . 5)))))
     (empty-event)
     (empty-event)
     (empty-event)))
  (test (walk x '() #f test-event) 5))

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

;; == STREAM TESTS =============================================================

(let ()
  (define a-inf (bindm empty-a (conj succeed succeed)))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list empty-a)))

(let ()
  (define a-inf (bindm empty-a (conj succeed (enforce (var 'x)))))
  (define ans (car (let ([stream (generator () (take/lazy a-inf))])
                     (take 1 stream))))
  (test (a-s ans) empty-s)
  (test (a-c ans) empty-c)
  (test (a-e ans) empty-e)
  (test ans empty-a))

(let ()
  (define a-inf (bindm empty-a (conj succeed (enforce (var 'x)) (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list '_.0)))

(let ()
  (define a-inf (bindm empty-a (conj (conde [succeed] [fail]) (enforce (var 'x)) (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list '_.0)))

(let ()
  (define a-inf (bindm empty-a (conj (conde [succeed] [succeed]) (enforce (var 'x)) (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 2 stream))
   (list '_.0 '_.0)))

(let ()
  (define a-inf (bindm empty-a (conj (conde [succeed] [succeed]) (enforce (var 'x)) (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take #f stream))
   (list '_.0 '_.0)))

(let ()
  (define a-inf 
    (bindm empty-a 
           (conj (onceo (conde [succeed] [succeed]))
                 (enforce (var 'x))
                 (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take #f stream))
   (list '_.0)))

(let ()
  (define a-inf 
    (bindm empty-a 
           (conj (onceo fail)
                 (enforce (var 'x))
                 (reify (var 'x)))))
  (test
   (let ([stream (generator () (take/lazy a-inf))])
     (take 1 stream))
   (list)))

;; == RUN TESTS ================================================================

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

;; == CONSTRAINT TESTS =========================================================

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

;; can constraints respond to multiple things within the same events
;; if they have multiple reactions
(test
 (run* (q)
   (exc9 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal rem-self (list q))
           (add-constraint-event/internal add-self (list q))))))
 '((_.0 : (reifiedc _.0 _.0))))

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

;; == CONSTRAINT INTERACTION TESTS =============================================

(let ()
  (define rands (list 5))
  (define-constraint (foo x) #:reified)

  (define-constraint (fooi [an-oc #:constant]) 
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
          (add-constraint (foo (+ (cadr an-oc) (cadr an-oc^)))))]
        [else 
         (fooi an-oc^)]))]
    #:reify 
    (if an-oc (cons 'foo (cdr an-oc)) #f))

  ;; (test (run* () (foo 5)) '([(foo 5)]))
  ;; (test (run* () (fooi #f) (foo 5)) '([(foo 5) (fooi (foo 5))]))

  (let ()
    (define a (car (run/internal 1 (fooi (cons foo rands)))))
    (define c (a-c a))
    (define fooi-rands (car (hash-ref c fooi)))
    (test (eq? (cdar fooi-rands) rands) #t))

  (let ()
    (define a (car (run/internal 1 (fooi #f) 
                     (send-event (add-constraint-event/internal foo rands)))))
    (define c (a-c a))
    (define fooi-rands (car (hash-ref c fooi)))
    (test (eq? (cdar fooi-rands) rands) #t))

  (test (run* () (fooi #f) (foo 5) (foo 6)) '([(foo 11)]))
  
  (test (run* () 
          (fooi #f)
          (send-event
           (composite-event
            (list (add-constraint-event/internal foo (list 5))
                  (add-constraint-event/internal foo (list 6))))))
        '([(foo 11)]))
  
  (test (run* () 
          (send-event
           (composite-event
            (list 
             (add-constraint-event/internal fooi (list #f))
             (add-constraint-event/internal foo (list 5))
             (add-constraint-event/internal foo (list 6))))))
        '(((foo 11))))
  
  (let ([rands (list 5)])
    (test (run* () 
            (send-event
             (composite-event
              (list 
               (add-constraint-event/internal fooi (list (cons foo rands)))
               (remove-constraint-event/internal foo rands)))))
          '(((fooi #f)))))

  (let ([rands (list 5)])
    (test (run* () 
            (send-event
             (composite-event
              (list 
               (add-constraint-event/internal fooi (list (cons foo rands)))
               (remove-constraint-event/internal foo rands)
               (add-constraint-event/internal foo (list 6))))))
          '([(foo 6) (fooi (foo 6))]))))

(let ()
  (define-constraint (foo x) #:reified)
  (define-constraint-interaction
    [(foo x) (foo y)] [(not (= x y)) [(foo (+ x y))]])

  (test (run* () (foo 5) (foo 5)) '(((foo 5 5))))
  (test (run* () (foo 5) (foo 6)) '(((foo 11))))

  ;; do constraint-interactions disappear on
  ;; remove-constraint-event/internal's when they shouldn't
  (let ([rands (list 5)])
    (test (run* () 
            (send-event (add-constraint-event/internal foo rands))
            (send-event (add-constraint-event/internal foo (list 5)))
            (send-event (remove-constraint-event/internal foo rands))
            (send-event (add-constraint-event/internal foo (list 6))))
          '(((foo 11))))))
