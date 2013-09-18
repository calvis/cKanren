#lang racket

(require 
 cKanren/src/framework
 cKanren/src/constraints
 cKanren/src/variables
 cKanren/src/package
 (except-in cKanren/src/infs make-a)
 cKanren/src/events
 cKanren/src/operators
 cKanren/src/running
 racket/generator
 "../tester.rkt")

(test
 (let ([stream (let ([a-inf (bindm empty-a (conj succeed succeed))])
                 (generator () (take/lazy a-inf)))])
   (take 1 stream))
 (list empty-a))

(test
 (let ([stream (let ([a-inf (bindm empty-a (conj succeed (enforce (var 'x))))])
                 (generator () (take/lazy a-inf)))])
   (take 1 stream))
 (list empty-a))

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

(define-constraint (exc1 x)
  #:reified)

(test
 (run 1 (q) (add-constraint (exc1 q)))
 '((_.0 : (exc1 _.0))))

(test
 (run* (q) (add-constraint (exc1 q)))
 '((_.0 : (exc1 _.0))))

(define-constraint (exc2 x)
  #:reified
  (cond
   [(not (var? x)) succeed]
   [else (add-constraint (exc2 x))]))

(test
 (run* (q) (add-association q 5) (exc2 q))
 '(5))

(define (check-store-empty rator)
  (lambda@ (a [s c q t e])
    (cond
     [(null? (filter/rator rator (constraint-store-c c))) a]
     [else (error 'test "constraint store not empty: ~a\n" c)])))

(test
 (run* (q) 
   (exc2 q) 
   (add-association q 5)
   (check-store-empty exc2))
 '(5))

(define-trigger (extr1 rator)
  [(add-constraint-event ra rn)
   (=> abort)
   (unless (eq? ra rator) (abort))])

(define-constraint (exc3 x)
  #:reaction
  [(extr1 exc1)
   (add-constraint (exc4 x))])

(define-constraint (exc4 x) #:reified)

(test
 (run* (q)
   (exc3 q)
   (exc1 q)
   (check-store-empty exc3))
 '((_.0 : (exc1 _.0) (exc4 _.0))))

(define-trigger (true-immediately)
  [(empty-event) #t])

(define-constraint (exc5 x)
  #:reaction
  [(true-immediately)
   (add-constraint (exc4 x))])

;; checks reactions that fire when you first enter the body of the
;; constraint (i.e. before the constraint is coming from the store)
(test
 (run* (q) 
   (exc5 q)
   (check-store-empty exc5))
 '((_.0 : (exc4 _.0))))

(define-trigger (rem-tr rator)
  [(remove-constraint-event/internal rator^ rands^)
   (=> abort)
   (unless (eq? rator rator^) (abort))])

(define-trigger (add-tr rator)
  [(add-constraint-event/internal rator^ rands^)
   (=> abort)
   (unless (eq? rator rator^) (abort))])

(define-constraint (exc6 x)
  #:reaction
  [(rem-tr exc6)
   (error 'test "should not see itself removed")])

(define-constraint (exc7 x)
  #:reaction
  [(add-tr exc7)
   (error 'test "should not see itself added")])

(test
 (run* (q)
   (let ([rator exc6]
         [rands (list q)])
     (conj (add-constraint (oc rator rands))
           (remove-constraint (oc rator rands)))))
 '(_.0))

(test
 (run* (q)
   (let ([rator exc7]
         [rands (list q)])
     (conj (add-constraint (oc rator rands))
           (remove-constraint (oc rator rands)))))
 '(_.0))

(define-constraint (exc8 x)
  #:reaction
  [(add-tr exc6)
   (add-constraint (exc1 x))]
  #:reaction
  [(add-tr exc7)
   (conj (add-constraint (exc1 x))
         (exc8 x))])

(test
 (run* (q)
   (exc8 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal exc7 (list q))
           (add-constraint-event/internal exc6 (list q)))))
   (check-store-empty exc8))
 '((_.0 : (exc1 _.0))))

(test
 (run* (q)
   (exc8 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal exc6 (list q))
           (add-constraint-event/internal exc7 (list q)))))
   (check-store-empty exc8))
 '((_.0 : (exc1 _.0))))

(define-constraint (exc9 x)
  #:reaction
  [(add-tr exc6)
   (conj (add-constraint (exc1 x))
         (add-constraint (exc9 x)))]
  #:reaction
  [(add-tr exc7)
   (conj (add-constraint (exc1 x))
         (add-constraint (exc9 x)))])

(test
 (run* (q)
   (exc9 q)
   (send-event (add-constraint-event/internal exc6 (list q))))
 '((_.0 : (exc1 _.0))))

(test
 (run* (q)
   (exc9 q)
   (send-event 
    (composite-event
     (list (add-constraint-event/internal exc6 (list q))
           (add-constraint-event/internal exc7 (list q))))))
 '((_.0 : (exc1 _.0 _.0))))

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
           (add-constraint (exc1 q)))])

  (test
   (run* (q)
     (exc16 q)
     (exc18 q)
     (exc17 q))
   '(_.0)))

