#lang racket

(require "constraints.rkt" "package.rkt" "mk-structs.rkt" "variables.rkt" "errors.rkt" 
         "infs.rkt" "helpers.rkt" "operators.rkt" "events.rkt" "substitution.rkt" "lex.rkt")
(require (for-syntax racket syntax/parse racket/syntax racket/match racket/function))
(require syntax/parse racket/syntax)

(require (rename-in (only-in racket filter) [filter ls:filter]))

(provide (all-defined-out))
(provide (for-syntax (all-defined-out)))

(define (sum lsct)
  (for/fold ([out succeed]) ([ct lsct])
    (conj ct out)))

;; defines a macro to create new unconstrained variables
(define-syntax fresh-aux
  (syntax-rules ()
    [(_ constructor (x ...) g g* ...)
     (let ([x (constructor (gensym 'x))] ...)
       (conj 
        (send-event (enter-scope-event x)) ...
        g g* ...
        (send-event (leave-scope-event x)) ...))]))

;; miniKanren's "fresh" defined in terms of fresh-aux over vars
(define-syntax-rule (fresh (x ...) g g* ...)
  (fresh-aux var (x ...) g g* ...))

(begin-for-syntax
 
 ;; package keyword matching
 (define-splicing-syntax-class package-keyword
   #:attributes (package)
   (pattern (~seq #:package (a:id [s:id c:id e:id]))
            #:with package #'(a [s c e]))
   (pattern (~seq #:package a:id)
            #:with (s c e) (generate-temporaries #'(?s ?c ?e))
            #:with package #'(a [s c e]))
   (pattern (~seq)
            #:with (a s c e) (generate-temporaries #'(?a ?s ?c ?e))
            #:with package #'(a [s c e])))
 
 (define-splicing-syntax-class reaction-keyword
   #:attributes (name [args 1] subs [response 1])
   (pattern (~seq #:reaction 
                  [(name args ...)
                   response ...])
            #:with subs
            #'(trigger-subs name)))

 (define-syntax-class (argument default-fn)
   #:attributes (arg fn)
   (pattern [arg:id #:constant] 
            #:with fn #'identity-update-fn)
   (pattern [arg:id fn])
   (pattern arg:id
            #:with fn default-fn))

 ;; constructor keyword matching
 (define-splicing-syntax-class constructor-keyword
   #:attributes (constructor)
   (pattern (~seq #:constructor constructor:id))
   (pattern (~seq) #:with constructor (generate-temporary #'?constfn)))

 (define-splicing-syntax-class persistent-keyword
   #:attributes (persistent?)
   (pattern (~seq (~and #:persistent persistent?:keyword)))
   (pattern (~seq) #:with persistent? #'#f))
 
 (define-splicing-syntax-class reification-keyword
   #:attributes (reified)
   (pattern (~seq #:reified)
            #:with reified #'#t)
   (pattern (~seq #:reification-function reified:expr))
   (pattern (~seq) #:with reified #'#f))

)

;; Event -> ConstraintTransformer
;; runs all the constraints on the event in the store, 
;; accumulating all their new events and then recurring
(define (send-event new-e)
  (lambda@ (a [s c q t e-orig])
    (cond
     ;; is the thing we are trying to send empty? if so, why send it
     [(empty-event? new-e) a]
     ;; if e-orig is empty we can run!
     [(empty-event? e-orig)
      (define store c)
      (define running-e (start-running new-e))
      (define send-to-all (conj send-to-running send-to-store solidify-event))
      (bindm (make-a s c q t running-e) send-to-all)]
     ;; if we are already running, don't try to run again. just add
     ;; the event we are trying to send to the waiting events
     [(running-event? e-orig)
      (make-a s c q t (compose-events new-e e-orig))]
     [else (error 'send-event "found unsent event: ~a\n" e-orig)])))

;; ConstraintTransformer
;; sends each running event to all other running events
(define send-to-running
  (lambda@ (a [s c q t e])
    (match-define (running-event r w) e)
    (cond
     [(composite-event? r)
      (bindm a (send-to-comp-event r))]
     [else a])))

;; Event -> ConstraintTransformer
(define (send-to-comp-event r)
  (match-define (composite-event es) r)
  (define (loop pre post)
    (match post
      [(list) succeed]
      [(cons e rest)
       (conj (send-to-other-events e (append pre rest))
             (loop (cons e pre) rest))]))
  (loop (list) es))

;; Event [List-of Event] -> ConstraintTransformer
(define (send-to-other-events e es)
  (define addcs 
    (filter add-constraint-event/internal? 
            (composite-event es))) ;; TODO: hack
  (define maybe-response
    (match-lambda
      [(add-constraint-event/internal rator rands)
       (define reaction (-constraint-reaction rator))
       (cond
        ;; is our kind of constraint generally interested in anything
        ;; inside of the event we have?
        [(reaction e)
         => ;; Response -> ConstraintTransformer
         (lambda (response)
           (run-response response rator (list rands)))]
        ;; if not, just use the accumulator
        [else succeed])]))
  (sum (map maybe-response addcs)))

;; ConstraintTransformer
(define solidify-event
  (lambda@ (a [s c q t e])
    (match-define (running-event r w) e)
    (define old-r
      (cond
       [(composite-event? r)
        (composite-event-es r)]
       [else (list r)]))
    (define new-r (solidify old-r w))
    (bindm (make-a s c q t (empty-event))
           (conj (sum (map solidify-atomic-event old-r))
                 (send-event new-r)))))

;; Event ConstraintStore -> ConstraintTransformer
(define send-to-store
  (lambda@ (a [s c q t e])
    (define store c)
    (define ct
      (for/fold 
        ([ct succeed]) 
        ([(rator rands*) store])
        (lambda@ (a [s c q t e])
          (match-define (running-event r w) e)
          (define reaction (-constraint-reaction rator))
          (cond
           ;; is our kind of constraint generally interested in anything
           ;; inside of the event we have?
           [(reaction r)
            => ;; Response -> ConstraintTransformer
            (lambda (response)
              (bindm a (conj (run-response response rator rands*) ct)))]
           ;; if not, just use the accumulator
           [else (bindm a ct)]))))
    (bindm a ct)))

;; Response Rator [List-of Rands] -> ConstraintTransformer
(define (run-response r rator rands*)
  (for/fold ([ct succeed]) ([rands rands*])
    (lambda@ (a [s c q t e]) ;; we need the e?
      (define removing-self?
        (match-lambda
          [(remove-constraint-event/internal rator^ rands^)
           (eq? rands rands^)]
          [else #f]))
      (define answer
        (cond
         ;; are we witnessing ourself be removed
         [(findf removing-self? e) ct]
         ;; is our constraint actually subscribed to our event?
         [(apply-response r rands a)
          => (match-lambda 
               [(list (cons tr* ct*) ...)
                ;; run-response-ct performs the changes the constraint
                ;; would like to see given the trigger.  our goal is to
                ;; capture what events it causes and chain them after the
                ;; trigger.
                (conj (for/fold 
                        ([answer succeed])
                        ([tr (reverse tr*)] [real-response (reverse ct*)])
                        (cond
                         ;; if the event we are trying to subscribe to still exists in the
                         ;; current event, then we run the responses from our rands
                         [(findf (curry eq? tr) e)
                          (conj (chain tr)
                                (remove-constraint (oc rator rands))
                                real-response
                                (unchain removing-self? answer))]
                         [else answer]))
                      ct)]
               [else (error 'run-response "~a" else)])]
         [else ct]))
      (bindm a answer))))

(define (chain tr)
  (lambda@ (a [s c q t e])
    (match-define (running-event r w) e)
    (define new-e 
      (running-event r (build-chain-event tr w (empty-event))))
    (make-a s c q t new-e)))

(define (unchain rs? ct)
  (lambda@ (a [s c q t e])
    (match-define (running-event r w) e)
    (match w
      [(build-chain-event tr old new)
       (define new-e (running-event r (apply-chain w)))
       (define new-a (make-a s c q t new-e))
       (cond
        [(findf rs? new) new-a]
        [else (bindm new-a ct)])]
      [else a])))

(define (apply-response r rands a)
  ((apply r rands) a))

(define (add-association x v)
  (let ([x (if (var? x) x v)]
        [v (if (var? x) v x)])
    (send-event (add-association-event x v))))

(define (add-constraint an-oc)
  (match-define (oc rator rands) an-oc)
  (send-event ((-constraint-add rator) rator rands)))

(define update-s
  (case-lambda
   [(u v)
    (lambda@ (a [s c q t e])
      (make-a (ext-s u v s) c q t e))]
   [(p) 
    (lambda@ (a [s c q t e])
      (make-a (ext-s* p s) c q t e))]))

(define (update-c new-oc)
  (lambda@ (a [s c q t e])
    (make-a s (ext-c new-oc c) q t e)))

(define (remove-from-c an-oc)
  (lambda@ (a [s c q t e])
    (make-a s (remq-c an-oc c) q t e)))

(define (remove-constraint an-oc)
  (match-define (oc rator rands) an-oc)
  (send-event ((-constraint-rem rator) rator rands)))

(define (enforce x)
  (lambda@ (a [s c q t e])
    a
    #;
    (let ([x (filter*/var? (walk x (substitution-s s)))])
      (bindm a (conj (add-event (enforce-event x)) send-event)))))

(define (reify x)
  (lambda@ (a [s c q t e])
    (when (not (empty-event? e))
      (error 'reify "internal error, event not empty ~a" e))
    (define v (walk* x s c e))
    (define r (reify-s v empty-s))
    (define v^ (reify-term v r))
    (define answer
      (cond
       [(null? r) v^]
       [else (reify-constraints v^ r c)]))
    answer))

;; reifies the substitution, returning the reified substitution
(define (reify-s v^ s)
  (define v (walk v^ s))
  (cond
   [(var? v) 
    `((,v . ,(reify-n v (size-s s))) . ,s)]
   [(mk-struct? v) 
    (define (k a d)
      (reify-s d (reify-s a s)))
    (recur v k)]
   [else s]))

(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar->str cvar) (number->string n))))

(define (reify-constraints v r store)
  (define store^ (run-reify-fns v r store))
  (cond
   [(null? store^) v] 
   [#t `(,v : . ,(sort-store store^))]
   [else `(,v . ,(sort-store store^))]))

;; sorts the constraint store by lex<=
(define (sort-store ocs) (sort ocs lex<= #:key car))

(define (run-reify-fns v r store)
  (hash->list
   (for*/fold
    ([h (hasheq)])
    ([(rator rands*) store]
     #:when (-constraint-reifyfn rator)
     [rands rands*])
    (define-values (sym ans)
      ((apply (-constraint-reifyfn rator) rands) v r))
    (cond
     [(any/var? ans) h]
     [else
      (define updatefn (curry insert-in-lex-order ans))
      (hash-update h sym updatefn '())]))))

;; given a new substitution and constraint store, adds the prefixes of
;; each to the existing substitution and constraint store. the
;; constraints in c-prefix still need to run
(define (update-package s^ c^)
  (lambda@ (a [s c q t e])
    (define s-prefix (prefix-s s s^))
    (define c-prefix (prefix-c c c^))
    (define add-event (add-substitution-prefix-event s-prefix))
    (bindm a (conj (send-event add-event) (sum c-prefix)))))

(define (identity-update-fn x . rest) x)

;; given a name and a way to update the constraint arguments
;; default-update-fn, expands to two macros to define constraints of
;; that type: one "name-constraint" macro that simply returns a
;; constraint, and one "define-name-constraint" that defines a
;; function that returns a constraint
(define-syntax (define-constraint-type stx)
  (syntax-parse stx
    [(define-constraint-type name:id default-update-fn:id)
     (define/with-syntax (definer add-name remove-name)
       (map (lambda (str) (format-id #'name str (syntax-e #'name)))
            (list "define-~a" "add-~a-event" "remove-~a-event")))
     #'(begin
         (struct name -constraint ())
         (define-constraint-events 
          add-name remove-name)
         (create-define-constraint 
          definer name default-update-fn add-name remove-name)
         (void))]))

(struct trigger (subs interp))

(define-for-syntax (parse-responses stx bindings)
  (syntax-parse stx
    [((~literal =>) stuff ...)
     #`(lambda (ans) 
         (unless (pair? ans)
           (error 'parse-responses "internal error: ~a\n" ans))
         ((let #,bindings stuff ...) 
          (car ans)))]
    [(stuff ...) 
     #`(lambda (ans) (let #,bindings stuff ...))]))

(define-syntax (create-define-constraint stx)
  (syntax-parse stx
    [(create-define-constraint definer struct-name ufn add rem)
     (syntax/loc stx
       (...
        (define-syntax (definer stx)
          (syntax-parse stx
            [(definer 
               (fn-name (~var args (argument #'ufn)) ...)
               (~seq (~or rkw:reaction-keyword
                          (~once pkgkw:package-keyword)
                          (~once reifykw:reification-keyword))
                     ...)
               body:expr ...)
             (define/with-syntax (a [s c e]) #'pkgkw.package)
             (define/with-syntax bindings
               #'([args.arg (args.fn args.arg s c e)] ...))
             (define/with-syntax (response ...)
               (map (curryr parse-responses #'bindings)
                    (syntax->list #'((rkw.response ...) ...))))
             ;; (pretty-print (syntax->datum #'(response ...)))
             (define/with-syntax reify-body
               (match (syntax-e #'reifykw.reified)
                 [#t #'(default-reify 'fn-name args.arg ...)]
                 [#f #f]
                 [_ #'(reifykw.reified ans r)]))
             (define/with-syntax reifyfn
               (cond
                [(syntax-e #'reify-body) 
                 #'(lambda (args.arg ...)
                     (lambda (ans r)
                       (let ([args.arg (args.fn args.arg r)] ...)
                         reify-body)))]
                [else #'#f]))
             (define should-sub-to-associations?
               (null? (syntax-e #'(rkw.subs ...))))
             (define/with-syntax reaction-length
               (length (syntax-e #'(rkw.name ...))))
             (define/with-syntax (index ...)
               (range 0 (syntax-e #'reaction-length)))
             (define/with-syntax reaction
               ;; Event -> Response
               ;; A Response is a 
               ;;   Rands ... -> Package -> [Vector (cons Event ConstraintTransformer)]
               ;; at this point, we are given an event that we vaguely
               ;; care about
               #`(lambda (e) 
                   (define all-matching-events 
                     (filter (lambda (e) 
                               (or (rkw.subs e) ... 
                                   #,@(cond
                                       [should-sub-to-associations?
                                        #'((association-event? e))]
                                       [else #'()])))
                             e))
                   ;; responses is either false or a function that
                   ;; takes the constraint arguments and then a
                   ;; package
                   (lambda (args.arg ...)
                     (lambda@ (a [s c q t e])
                       (define rets
                         (for/fold 
                           ([rets (make-vector (add1 reaction-length) (list))])
                           ([an-e all-matching-events])
                           (cond
                            [((bindm a ((trigger-interp rkw.name) rkw.args ...)) an-e)
                             => 
                             (lambda (ans)
                               (define ret (cons an-e (response ans)))
                               (vector-set! rets index
                                            (cons ret (vector-ref rets index)))
                               rets)]
                            ...
                            [(and (association-event? an-e)
                                  (contains-relevant-var?
                                   an-e
                                   (filter*/var? (list args.arg ...))))
                             (define ret
                               (cons an-e 
                                     (let ([args.arg (args.fn args.arg s c an-e)] ...)
                                       (add-constraint (fn-name args.arg ...)) 
                                       body ...)))
                             (vector-set! rets reaction-length 
                                          (cons ret (vector-ref rets reaction-length)))
                             rets]
                            [else rets])))
                       ;; rets
                       (define rets^
                         (for/fold ([all '()]) ([ls rets])
                           (append all ls)))
                       (and (not (null? rets^)) rets^)))))
             (define/with-syntax pattern
               #'(define fn-name
                   (let ()
                     (struct fn-name-struct struct-name ()
                             #:methods gen:custom-write 
                             [(define (write-proc this port mode)
                                ((parse-mode mode) 'fn-name port))])
                     (fn-name-struct
                      (lambda (args.arg ...)
                        (lambda@ (a [s c q t e])
                          (define entire-body
                            (let ([args.arg (args.fn args.arg s c e)] ...)
                              (add-constraint (fn-name args.arg ...)) 
                              body ...))
                          (cond
                           ;; okay HERE, do an EXHAUSTIVE search + the
                           ;; empty-event and the an-es that you get
                           ;; BACK from the reaction should include
                           ;; all the chains they had to go thru to
                           ;; exist.  unless it was the empty-event in
                           ;; which case have a SPECIAL line for that
                           ;; and attribute it to nothing.
                           [(cond
                             [(reaction e)
                              => (lambda (a-response)
                                   ((a-response args.arg ...) a))])
                            => (match-lambda
                                 [(list (cons an-e ct) (... ...))
                                  (bindm a (sum ct))]
                                 [else (error 'here "HERERERRR")])]
                           [(cond
                             [(reaction (empty-event))
                              => (lambda (a-response)
                                   ((a-response args.arg ...) a))])
                            => (match-lambda
                                 [(list (cons an-e ct) (... ...))
                                  (bindm a (sum ct))]
                                 [else (error 'here "efdfHERERERRR")])]
                           [else (bindm a entire-body)])))
                      reaction
                      reifyfn
                      add 
                      rem))))
             ;; (pretty-print (syntax->datum #'pattern))
             #'pattern]))))]))

;; TODO, weird scope of package (should be an error to try to use it
;; in event-names)
(define-syntax (define-trigger stx)
  (syntax-parse stx
    [(define-trigger (name args ...)
       (~seq (~or (~once pkgkw:package-keyword))
             ...)
       [(event-name:id event-arg ...)
        (~optional ((~literal =>) abort)
                   #:defaults ([abort (generate-temporary #'?abort)]))
        answer answer* ...]
       ...)
     (define/with-syntax (a [s c e]) #'pkgkw.package)
     (define/with-syntax pattern
       #'(define name
           (trigger 
            (lambda (e)
              (let ([ans (match e
                           [(struct event-name _) #t]
                           ...
                           [_ #f])])
                ans))
            (lambda (args ...)
              (lambda@ (a [s c q t e]) 
                (match-lambda
                  [(event-name event-arg ...)
                   (=> abort)
                   (let ([result (let () answer answer* ...)])
                     (list result))]
                  ;; TODO WRONGGGG, TODO: WHY
                  ...
                  [_ #f]))))))
     #'pattern]))

(define-syntax (transformer stx)
  (syntax-parse stx
    [(transformer 
      (~seq (~or (~once pkgkw:package-keyword))
            ...)
      body:expr ...)
     (define/with-syntax (a [s c e]) #'pkgkw.package)
     #'(lambda@ (a [s c q t e])
         (bindm a (let () body ...)))]))

(define (default-reify sym . args)
  (define reified-rands
    (cond
     [(null? args) args]
     [(null? (cdr args)) (car args)]
     [else args]))
  (values sym reified-rands))

(define-constraint-type constraint walk*)

;; Event -> ConstraintTransformer
(define/match (solidify-atomic-event e)
  [((add-association-event u v)) (update-s u v)]
  [((add-substitution-prefix-event p)) (update-s p)]
  [((add-constraint-event/internal rator rands))
   (update-c (oc rator rands))]
  [((remove-constraint-event/internal rator rands)) 
   (remove-from-c (oc rator rands))]
  [((empty-event)) succeed]
  [(e) succeed])

(define-trigger (enter-scope x)
  [(enter-scope-event y)
   (=> abort) (unless (or (not x) (eq? x y)) (abort)) y])

(define-trigger (leave-scope x)
  [(leave-scope-event y)
   (=> abort) (unless (or (not x) (eq? x y)) (abort)) y])

(define-trigger (any-association-event x)
  [(add-association-event y z)
   (=> abort)
   (unless (or (eq? x y) (memq x (filter*/var? z)))
     (abort))
   (list (cons y z))]
  [(add-substitution-prefix-event p)
   (=> abort)
   (define (assoc-contains-var? u/v)
     (or (eq? x (car u/v)) (memq x (filter*/var? (cdr u/v)))))
   (cond
    [(ls:filter assoc-contains-var? p)
     => (lambda (p) (when (null? p) (abort)) p)]
    [else (abort)])])



