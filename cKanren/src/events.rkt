#lang racket

(require "variables.rkt" "constraints.rkt")
(require racket/generic)
(require (for-syntax syntax/parse racket/syntax racket/match racket/pretty racket/function))
(provide (all-defined-out))

;; a generic interface for Events
(define-generics event
  ;; Event Event -> [Maybe Event]
  ;; optimistically merges event and e, which cancels out events
  ;; wherever possible.  additional constraint that (e< event e) holds.
  (gen-optimistic-merge event e relation)

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
  [(define (gen-optimistic-merge e e^ relation)
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
(define (optimistic-merge e e^ [relation eq?])
  (cond
   [(<e e e^)
    (gen-optimistic-merge e^ e relation)]
   [else (gen-optimistic-merge e e^ relation)]))

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
  (or (and (fn e) e) (gen-findf fn e ce)))

;; [Event -> Boolean] Event -> [List-of Event]
(define (filter fn e)
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
   [(composite-event? e) #f]
   [(composite-event? e^) #t]
   [else #t]))

;; first try optimistically merging the events, then pessimistically
(define (compose-events e e^)
  (cond
   [(and (composite-event? e)
         (composite-event? e^))
    (for/fold ([comp e]) ([e-inner (composite-event-es e^)])
      (compose-events comp e-inner))]
   [else
    (or (optimistic-merge e e^)
        (pessimistic-merge e e^))]))

;; STRUCTURES ==================================================================

(struct empty-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^ relation) #f)
         (define (gen-pessimistic-merge e e^) e^)
         (define (gen-findf fn e ce) #f)])

(define empty-e (empty-event))

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
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (composite-event es) e)
           (cond
            [(map-maybe (lambda (e) (optimistic-merge e e^ relation)) es)
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

(struct add-substitution-prefix-event (p)
        #:transparent
        #:methods gen:event 
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (add-substitution-prefix-event p) e)
           (match e^
             [(add-substitution-prefix-event p^)
              (add-substitution-prefix-event (append p p^))]
             [_ #f]))]
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
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (running-event r w) e)
           (cond
             [(optimistic-merge r e^ relation)
              => (curryr running-event w)]
             [(optimistic-merge w e^ relation)
              => (curry running-event r)]
             [else #f]))
         (define (gen-pessimistic-merge e e^)
           (match-define (running-event r w) e)
           (running-event r (pessimistic-merge w e^)))
         (define (gen-findf fn e ce)
           (match-define (running-event r w) e)
           (findf fn r ce))
         (define (gen-filter fn e)
           (match-define (running-event r w) e)
           (filter fn r))]
        #:methods gen:compound-event [])

(define (relevant? x e)
  (and (association-event? e)
       (contains-relevant-var? e (list x))))

(struct constraint-event (rator rands)
        #:transparent
        #:methods gen:event [])

(struct add-constraint-event/internal constraint-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (add-constraint-event/internal rator rands) e)
           (match e^
             [(remove-constraint-event/internal rator^ rands^)
              (and (eq? rator rator^) (relation rands rands^) (empty-event))]
             [_ #f]))])

(struct remove-constraint-event/internal constraint-event ()
        #:transparent
        #:methods gen:event
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (remove-constraint-event/internal rator rands) e)
           (match e^
             [(add-constraint-event/internal rator^ rands^)
              (and (eq? rator rator^) (relation rands rands^) (empty-event))]
             [_ #f]))])

(define-syntax (define-constraint-events stx)
  (syntax-parse stx
    [(define-new-constraint-event add-name:id remove-name:id)
     #'(begin
         (struct add-name add-constraint-event/internal ()
                 #:transparent)
         (struct remove-name remove-constraint-event/internal ()
                 #:transparent))]))

(struct build-chain-event running-event (trigger new)
        #:transparent
        #:methods gen:event 
        [(define (gen-optimistic-merge e e^ relation)
           (match-define (build-chain-event r w tr new) e)
           (cond
            ;; only if we have totally removed the trigger can we
            ;; cancel the chain build
            [(empty-event? (optimistic-merge tr e^ relation))
             (running-event (optimistic-merge r e^ relation)
                            (compose-events w new))]
            [(optimistic-merge new e^ equal?)
             => (curry build-chain-event r w tr)]
            [else #f]))
         ;; we can only be here if we have willingly gone into the
         ;; waiting event of a running event. so continue on.
         (define (gen-findf fn e ce)
           (match-define (build-chain-event r w tr new) e)
           (or (findf fn r) (findf fn new) (findf fn w tr)))
         (define (gen-pessimistic-merge e e^)
           (match-define (build-chain-event r w tr new) e)
           (build-chain-event r w tr (pessimistic-merge new e^)))
         (define (gen-filter fn e)
           (match-define (running-event r w) e)
           (filter fn r))])

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
            [else (empty-event)]
            ;; [else (chain-event head (solidify solid tail))]
            ))
         (define (gen-remove-chains e)
           (empty-event))]
        #:methods gen:compound-event [])

;; Event -> Event
;; replace trigger with (chain-event trigger stored)
(define (apply-chain e)
  (match-define (build-chain-event r w tr new) e)
  (running-event r (compose-events w (chain-event tr new))))

;; [List-of Event] Event -> Event
(define (solidify solid e)
  (gen-solidify solid e))

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


(struct enforce-event (xs)
        #:methods gen:event [])

(struct enforce-in-event enforce-event ())
(struct enforce-out-event enforce-event ())

