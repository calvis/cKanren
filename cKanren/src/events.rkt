#lang racket

(require "variables.rkt" "constraints.rkt")
(require racket/generic)
(require (for-syntax syntax/parse racket/syntax racket/match racket/pretty racket/function))
(provide (all-defined-out))

;; sets up some constants to use in testing
(module+ test
  (require (prefix-in ru: rackunit))
  
  (define rator1 (lambda (x) x))
  (define rands1 (list 5))
  (define rator2 (lambda (x) x))
  (define rands2 (list 6)))

;; a generic interface for Events
(define-generics event
  ;; Event Event -> [Maybe Event]
  ;; optimistically merges event and e, which cancels out events
  ;; wherever possible.  additional constraint that (e< event e) holds.
  (gen-optimistic-merge event e)

  ;; Event Event -> Event
  ;; pessimistically merges event and e, which just shoves them
  ;; together into a single event.  cannot fail.
  (gen-pessimistic-merge event e)

  ;; [Event -> Boolean] Event [Maybe Event] -> [Maybe Event]
  ;; finds an event inside the argument event that satisfies fn, if it exists
  ;; will look inside chain events off of ce if building a chain for ce
  (gen-findf fn event ce)

  ;; [Event -> Boolean] Event -> [List-of Event]
  ;; returns a list of all sub-events of event that satisfy fn
  (gen-filter fn event)

  ;; [List-of Event] Event -> Event
  ;; unchains any events in event whose heads are in solid
  (gen-solidify solid event)

  ;; Event -> Event
  ;; removes all of the unfounded chains from an event about to be sent
  (gen-remove-chains event)

  #:fallbacks
  [(define (gen-optimistic-merge e e^)
     #f)
   (define (gen-pessimistic-merge e e^)
     (make-composite-event (list e e^)))
   (define (gen-findf fn e ce)
     (and (fn e) e))
   (define (gen-filter fn e)
     (if (fn e) (list e) (list)))
   (define (gen-solidify solid e) e)
   (define (gen-remove-chains e) e)])

(define-generics compound-event)

(define-generics association-event
  (contains-relevant-var? association-event vars)
  (walk/shortcut u association-event))

;; Event Event -> [Maybe Event]
(define (optimistic-merge e e^)
  (cond
   [(<e e e^)
    (gen-optimistic-merge e^ e)]
   [else (gen-optimistic-merge e e^)]))

;; Event Event -> Event
(define (pessimistic-merge e e^)
  (cond
   [(empty-event? e) e^]
   [(empty-event? e^) e]
   [(<e e e^)
    (gen-pessimistic-merge e^ e)]
   [else (gen-pessimistic-merge e e^)]))

;; [Event -> Boolean] Event -> [Maybe Event]
(define (findf fn e [ce #f])
  (unless (event? e)
    (error 'findf "not an event: ~a" e))
  (or (and (fn e) e) (gen-findf fn e ce)))

;; [Event -> Boolean] Event -> [List-of Event]
(define (filter fn e)
  (unless (event? e)
    (error 'filter "not an event: ~a" e))
  (cond 
   [(compound-event? e)
    (gen-filter fn e)]
   [(fn e) (list e)]
   [else '()]))

;; orders priority of events
;; where: chain-events > running-event > composite-event > anything else
(define (<e e e^)
  (cond
   [(running-event? e) #f]
   [(running-event? e^) #t]
   [(build-chain-event? e) #f]
   [(build-chain-event? e^) #t]
   [(composite-event? e) #f]
   [(composite-event? e^) #t]
   [else #t]))

;; first try optimistically merging the events, then pessimistically
(define (compose-events e e^)
  (unless (and (event? e) (event? e^))
    (error 'compose-events "wut no ~s ~s\n" e e^))
  (cond
   [(and (composite-event? e)
         (composite-event? e^))
    (for/fold ([comp e]) ([e-inner (composite-event-es e^)])
      (compose-events comp e-inner))]
   [else
    (or (optimistic-merge e e^)
        (pessimistic-merge e e^))]))
(require racket/trace)
;; (trace compose-events)

(module+ test
  (ru:check-equal?
   (compose-events
    (constraint-event rator1 rands1)
    (running-event (add-association-event 'q 5) (empty-event)))
   (running-event
    (add-association-event 'q 5)
    (constraint-event rator1 rands1))))

;; STRUCTURES ==================================================================

(struct empty-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^) #f)
         (define (gen-pessimistic-merge e e^) e^)
         (define (gen-findf fn e ce) #f)])

(define empty-e (empty-event))

(module+ test
  (ru:check-true
   (<e (empty-event)
       (running-event (empty-event) (empty-event))))
  (ru:check-true
   (<e (composite-event (list (empty-event) (empty-event)))
       (running-event (empty-event) (empty-event))))
  #;
  (ru:check-true
   (<e (remove-constraint-event rators1 rands1)
       (composite-event (list (empty-event) (empty-event)))))
  ;; TODO: MORE EXAMPLES
  (ru:check-equal? 
   (pessimistic-merge (empty-event) (empty-event))
   (empty-event)))
  
(define (make-composite-event es)
  (cond
   [(null? es)
    (empty-event)]
   [(null? (cdr es))
    (car es)]
   [else (composite-event es)]))

(define (map-maybe fn es)
  (cond
   [(null? es) #f]
   [(fn (car es))
    => (lambda (e^)
         (cond
          [(empty-event? e^) (cdr es)]
          [else (cons e^ (cdr es))]))]
   [(map-maybe fn (cdr es))
    => (curry cons (car es))]
   [else #f]))

(struct composite-event (es)
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^)
           (match-define (composite-event es) e)
           (cond
            [(map-maybe (curry optimistic-merge e^) es)
             => (curry make-composite-event)]
            [else #f]))
         (define (gen-pessimistic-merge e e^)
           (match-define (composite-event es) e)
           (cond
            [(empty-event? e^) e]
            [else (make-composite-event (cons e^ es))]))
         (define (gen-findf fn e ce)
           (match-define (composite-event es) e)
           (ormap (lambda (e) (findf fn e ce)) es))
         (define (gen-filter fn e)
           (match-define (composite-event es) e)
           (append-map (curry filter fn) es))
         (define (gen-solidify solid e)
           (match-define (composite-event es) e)
           (for/fold ([new-e (empty-event)]) ([e es])
             (compose-events new-e (solidify solid e))))
         (define (gen-remove-chains e)
           (match-define (composite-event es) e)
           (for/fold ([new-e (empty-event)]) ([e es])
             (compose-events new-e (remove-chains e))))]
        #:methods gen:compound-event [])

(struct add-association-event (x v)
        #:transparent
        #:methods gen:event []
        #:methods gen:association-event
        [(define (contains-relevant-var? e vars)
           (match-define (add-association-event x v) e)
           (memq x vars))
         (define (walk/shortcut u e)
           (match-define (add-association-event x v) e)
           (and (eq? u x) v))])

(struct add-substitution-prefix-event (p)
        #:transparent
        #:methods gen:event []
        #:methods gen:association-event
        [(define (contains-relevant-var? e vars)
           (match-define (add-substitution-prefix-event p) e)
           (define ((assoc-contains-var? u/v) x) (eq? x (car u/v)))
           (ormap (lambda (u/v) (ormap (assoc-contains-var? u/v) vars)) p))
         (define (walk/shortcut u e)
           (match-define (add-substitution-prefix-event p) e)
           (cond [(assq u p) => cdr] [else #f]))])

(define (<rp e e^)
  (cond
   [(association-event? e^) #f]
   [(association-event? e) #t]
   [else #f]))

(define (start-running e) 
  (running-event (remove-chains e) (empty-event)))

(define (remove-chains e)
  (gen-remove-chains e))

(struct running-event (r w) 
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^)
           (match-define (running-event r w) e)
           (match w
             [(build-chain-event tr old new)
              (=> abort)
              (cond
               [(optimistic-merge tr e^)
                (running-event
                 (optimistic-merge r e^)
                 (compose-events old new))]
               [else (abort)])]
             [_
              (cond
               [(optimistic-merge r e^)
                => (curryr running-event w)]
               [(optimistic-merge w e^)
                => (curry running-event r)]
               [else #f])]))
         (define (gen-pessimistic-merge e e^)
           (match-define (running-event r w) e)
           (running-event r (pessimistic-merge w e^)))
         (define (gen-findf fn e ce)
           (match-define (running-event r w) e)
           (or (findf fn r ce)
               (match w
                 [(build-chain-event tr old new)
                  (or (findf fn new ce)
                      (findf fn old tr))]
                 [else #f])))
         (define (gen-filter fn e)
           (match-define (running-event r w) e)
           (filter fn r))
         (define (gen-solidify solid e)
           (error 'gen-solidify "internal error: ~a" e))]
        #:methods gen:compound-event [])

(module+ test
  (ru:check-equal?
   (findf 
    association-event?
    (running-event
     (add-substitution-prefix-event '())
     (empty-event)))
   (add-substitution-prefix-event '()))
  
  (let ([u (var 'u)])
    (ru:check-equal?
     (findf
      (curryr relevant? u)
      (running-event
       (add-substitution-prefix-event `((,u . a)))
       (build-chain-event
        (add-substitution-prefix-event '())
        (empty-event)
        (composite-event
         (list
          (add-substitution-prefix-event `((,u . b)))
          (remove-constraint-event/internal rator1 rands1))))))
     (add-substitution-prefix-event `((,u . a)))))

  (let ([u (var 'u)])
    (ru:check-equal?
     (findf
      (curryr relevant? u)
      (running-event
       (add-substitution-prefix-event '())
       (build-chain-event
        (add-substitution-prefix-event '())
        (empty-event)
        (composite-event
         (list
          (add-substitution-prefix-event `((,u . a)))
          (remove-constraint-event/internal rator1 rands1))))))
     (add-substitution-prefix-event `((,u . a)))))

  (let ([u (var 'u)]
        [ce (add-substitution-prefix-event '())])
    (ru:check-equal?
     (findf
      (curryr relevant? u)
      (build-chain-event
       ce
       (chain-event 
        ce
        (add-substitution-prefix-event `((,u . a))))
       (empty-event)))
     (add-substitution-prefix-event `((,u . a)))))

  (let ([u (var 'u)]
        [ce (add-substitution-prefix-event '())])
    (ru:check-equal?
     (findf
      (curryr relevant? u)
      (running-event
       (empty-event)
       (build-chain-event
        ce
        (chain-event 
         ce
         (add-substitution-prefix-event `((,u . a))))
        (empty-event))))
     (add-substitution-prefix-event `((,u . a))))))

(define (relevant? x)
  (lambda (e)
    (and (association-event? e)
         (contains-relevant-var? e (list x)))))

(struct constraint-event (rator rands)
        #:transparent
        #:methods gen:event [])

(struct add-constraint-event/internal constraint-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^)
           (match-define (add-constraint-event/internal rator rands) e)
           (match e^
             [(remove-constraint-event/internal
               rator^ rands^)
              (and (eq? rator rator^)
                   (equal? rands rands^)
                   (empty-event))]
             [_ #f]))])

(struct remove-constraint-event/internal constraint-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^)
           (match-define (remove-constraint-event/internal rator rands) e)
           (match e^
             [(add-constraint-event/internal
               rator^ rands^)
              (and (eq? rator rator^)
                   (equal? rands rands^)
                   (empty-event))]
             [_ #f]))])

(define-syntax (define-constraint-events stx)
  (syntax-parse stx
    [(define-new-constraint-event add-name:id remove-name:id)
     #'(begin
         (struct add-name add-constraint-event/internal ()
                 #:transparent)
         (struct remove-name remove-constraint-event/internal ()
                 #:transparent))]))

(struct build-chain-event (trigger old new)
        #:transparent
        #:methods gen:event 
        [(define (gen-optimistic-merge e e^)
           (match-define (build-chain-event trigger old new) e)
           (cond
            [(optimistic-merge new e^)
             => (curry build-chain-event trigger old)]
            [else #f]))
         ;; we can only be here if we have willingly gone into the
         ;; waiting event of a running event. so continue on.
         (define (gen-findf fn e ce)
           (match-define (build-chain-event trigger old new) e)
           (or (findf fn new) (findf fn old trigger)))
         (define (gen-pessimistic-merge e e^)
           (match-define (build-chain-event trigger old new) e)
           (build-chain-event trigger old (pessimistic-merge new e^)))])

(module+ test
  (ru:check-equal?
   (compose-events
    (build-chain-event
     (add-association-event 'q 5)
     (running-event
      (add-association-event 'q 5)
      (empty-event))
     (empty-event))
    (constraint-event rator1 rands1))
   (build-chain-event
    (add-association-event 'q 5)
    (running-event
     (add-association-event 'q 5)
     (empty-event))
    (constraint-event rator1 rands1))))

(struct chain-event (head tail)
        #:transparent
        #:methods gen:event 
        [(define (gen-findf fn e ce)
           (match-define (chain-event head tail) e)
           (and ce (eq? ce head) (findf fn tail ce)))
         (define (gen-solidify solid e)
           (match-define (chain-event head tail) e)
           (cond
            [(memq head solid) (solidify solid tail)]
            [else (chain-event head (solidify solid tail))]))
         (define (gen-remove-chains e)
           (empty-event))]
        #:methods gen:compound-event [])

;; Event -> Event
;; replace trigger with (chain-event trigger stored)
(define (apply-chain e)
  (match-define (build-chain-event trigger old new) e)
  (compose-events old (chain-event trigger new)))

(module+ test
  (let ([trigger (add-association-event 'q 5)])
    (ru:check-equal?
     (apply-chain
      (build-chain-event
       trigger
       (empty-event)
       (composite-event
        (list
         (constraint-event rator1 rands2)
         (constraint-event rator1 rands1)))))
     (chain-event
      trigger
      (composite-event
       (list
        (constraint-event rator1 rands2)
        (constraint-event rator1 rands1)))))))

;; [List-of Event] Event -> Event
(define (solidify solid e)
  (gen-solidify solid e))
;; (trace solidify)

(module+ test
  (let ([tr (add-association-event 'q 5)])
    (ru:check-equal?
     (solidify
      (list tr)
      (chain-event tr (add-association-event 'q 6)))
     (add-association-event 'q 6)))

  (let ([trigger1 (add-association-event 'q 5)]
        [trigger2 (add-constraint-event/internal rator1 rands1)])
    (ru:check-equal?
     (solidify
      (list trigger1 trigger2)
      (composite-event
       (list (chain-event trigger1 (add-association-event 'q 6))
             (chain-event trigger2 (chain-event trigger1 (add-association-event 'q 7))))))
     (composite-event
      (list (add-association-event 'q 7)
            (add-association-event 'q 6))))))


(struct enter-scope-event (x)
        #:transparent
        #:methods gen:event [])

(struct leave-scope-event (x)
        #:transparent
        #:methods gen:event [])

(define-syntax-rule (define-event name (args ...))
  (struct name (args ...)
          #:transparent
          #:methods gen:event []))
