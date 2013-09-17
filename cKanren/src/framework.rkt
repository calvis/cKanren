#lang racket

(require "attributes.rkt" "constraints.rkt" "goals.rkt" "package.rkt" 
         "mk-structs.rkt" "ocs.rkt" "variables.rkt" "errors.rkt" 
         "infs.rkt" "helpers.rkt" "operators.rkt" "events.rkt")
(require racket/generator (prefix-in ru: rackunit))
(require (for-syntax syntax/parse racket/syntax racket/match))
(require syntax/parse racket/syntax)

(provide (all-defined-out))

;; runs all the constraints on the event in the store, 
;; accumulating all their new events and then recurring
(define send-event
  (lambda@ (a [s c q t e-orig])
    (cond
     [(not e-orig) a]
     [else 
      (define store (constraint-store-c c))
      (define apply-to-store
        (for/fold ([fn send-event]) ([(keys ocs) store])
          (for/fold ([fn fn]) ([oc ocs])
            (lambda@ (a [s c q t e])
              (cond
               [((oc-subs oc) e-orig)
                (bindm 
                  (make-a s c q t e-orig) 
                  (conj (rem/run oc) (add-event e)))]
               [else a])))))
      (bindm (make-a s c q t #f) apply-to-store)])))

;; adds an event to the event in the package
(define (add-event e^)
  (lambda@ (a [s c q t e])
    (make-a s c q t (compose-events e e^))))

;; removes oc from the constraint store and then runs it
(define (rem/run oc)
  (lambda@ (a [s c q t e])
    (define ocs (constraint-store-c c))
    (cond
     [(memq-c oc ocs)
      (define new-c (constraint-store (remq-c oc ocs)))
      (define new-e (compose-events (remove-constraint-event oc) e))
      (bindm (make-a s new-c q t new-e) (oc-proc oc))]
     [else a])))

;; updates the substitution with a binding of x to v
(define (update-s x v)
  (lambda@ (a [s c q t e])
    (define old-s (substitution-s s))
    (define new-s (substitution (ext-s x v old-s)))
    (define new-e (compose-events (add-association-event x v) e))
    (bindm (make-a new-s c q t new-e) send-event)))

(define (update-c oc)
  (lambda@ (a [s c q t e])
    (cond
     [(event? oc)
      (define old-c (constraint-store-c c))
      (define new-c (ext-c (remove-constraint-event-oc oc) old-c))
      (make-a s (constraint-store new-c) q t (remove-remove-event oc e))]
     [else 
      (define old-c (constraint-store-c c))
      (define new-c (ext-c oc old-c))
      (define new-e (add-constraint-event oc))
      (bindm 
        (make-a s (constraint-store new-c) q t new-e)
        send-event)])))

;; TODO: not efficient
(define (remove-remove-event oc e)
  (match e
    [(remove-constraint-event oc^)
     (cond
      [(eq? oc oc^) #f]
      [else e])]
    [(composite-event ls)
     (map (curry remove-remove-event oc) ls)]
    [_ e]))

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
 
 ;; argument keyword matching
 (define-splicing-syntax-class (arguments-keyword default-fn)
   #:attributes (bindings)
   (pattern (~seq #:args ((~var bd (argument default-fn)) ...))
            #:with bindings #'((bd.arg1 bd.arg2 bd.fn) ...))
   (pattern (~seq)
            #:with bindings #'()))

 (define-syntax-class (argument default-fn)
   #:attributes (arg1 arg2 fn)
   (pattern (arg1:id #:constant) 
            #:with fn #'(lambda (x . rest) x)
            #:with arg2 #'arg1)
   (pattern (arg1:id arg2:id fn:id))
   (pattern (arg1:id fn:id)
            #:with arg2 (generate-temporary #'?arg^))
   (pattern arg1:id 
            #:with fn default-fn
            #:with arg2 (generate-temporary #'?arg^)))

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
   #:attributes (rfn)
   (pattern (~seq (~and #:reified rfn:keyword)))
   (pattern (~seq #:reification-function rfn:expr))
   (pattern (~seq) #:with rfn #'#f))

 (define-splicing-syntax-class (constraint-options ufn)
   #:attributes (options)
   (pattern (~seq (~or
                   (~once pkgkw:package-keyword)
                   (~once pkw:persistent-keyword)
                   (~once rkw:reification-keyword)
                   (~once ckw:constructor-keyword)
                   (~once (~var argskw (arguments-keyword ufn))))
                  ...)
            #:with options
            #`(#:package pkgkw.package
               #:args argskw.bindings
               #:constructor ckw.constructor
               #:persistent pkw.persistent? 
               #:reified rkw.rfn)))

 (define-splicing-syntax-class define-constraint-options
   (pattern (~seq (~or
                   (~once pkw:persistent-keyword)
                   (~once rkw:reification-keyword)
                   (~once pkgkw:package-keyword))
                  ...)))
)

;; given a name and a way to update the constraint arguments
;; default-update-fn, expands to two macros to define constraints of
;; that type: one "name-constraint" macro that simply returns a
;; constraint, and one "define-name-constraint" that defines a
;; function that returns a constraint
(define-syntax (define-constraint-type stx)
  (syntax-parse stx
    [(define-constraint-type name:id default-update-fn:expr)
     (define/with-syntax definer 
       (format-id #'name "define-~a" (syntax-e #'name)))
     #'(begin
         (define fn default-update-fn)
         (create-constraint name fn)
         (create-define-constraint definer name fn))]))

(define-syntax (create-constraint stx)
  (syntax-parse stx
    [(create-constraint name ufn)
     #'(...
        (define-syntax (name stx)
          (syntax-parse stx
            [(name (~var opts (constraint-options #'ufn)) body:expr ...)
             (define/with-syntax (options ...) #'opts.options)
             #'(constraint/internal 
                [options ...] 
                body ...)])))]))

(define-syntax (create-define-constraint stx)
  (syntax-parse stx
    [(create-define-constraint definer name fn)
     (syntax/loc stx
       (...
        (define-syntax (definer stx)
          (syntax-parse stx
            [(definer (fn-name (~var args (argument #'fn)) ...)
               opt:define-constraint-options
               body:expr ...)
             (define/with-syntax (options ...) #'opt)
             (syntax/loc stx
               (define (fn-name args.arg2 ...)
                 (name
                  options ...
                  #:constructor fn-name
                  #:args ((args.arg1 args.arg2 args.fn) ...)
                  body ...)))]))))]))

(define-syntax (constraint/internal stx)
  (syntax-parse stx
    [(create/internal
      [#:package (a [s c e])
       #:args ((args:id args^:id fn:id) ...)
       #:constructor constfn
       #:persistent stx-persistent?
       #:reified stx-reified
       ;; #:unique stx-unique?
       ] 
      body ...)
     ;; (define persistent? (syntax-e stx-persistent?))
     ;; (define reified? (syntax-e stx-reified?))
     ;; (define unique? (syntax-e stx-unique?))
     (define/with-syntax reify-body
       (match (syntax-e #'stx-reified)
         ['#:reified #'(default-reify 'constfn args ...)]
         [#f #f]
         [_ #'stx-reified]))
     (define/with-syntax entire-body
       (cond
        [(syntax-e #'stx-persistent?)
         #'(conj
            (let () succeed body ...)
            (update-c (constfn args ...)))]
        [else #'(let () succeed body ...)]))
     #`(letrec ([constraint-expression
                 (lambda@ (a [subst store q t e])
                   (define s (substitution-s subst))
                   (define c (constraint-store-c store))
                   (define reifyfn 
                     #,(cond
                        [(syntax-e #'reify-body) 
                         #'(lambda (args^ ...)
                             (lambda (ans r)
                               (let ([args (fn args^ r c e)] ...)
                                 (reify-body ans r))))]
                        [else #'#f]))
                   (let ([constfn
                          (lambda (args ...)
                            (define old-args (list args^ ...))
                            (define new-args (list args ...))
                            (define event (no-op-event 'constfn new-args old-args e))
                            (or event (build-oc constfn reifyfn args ...)))]
                         [args (fn args^ s c e)] ...)
                     (bindm a entire-body)))]
                [constfn (lambda (args ...) constraint-expression)])
         constraint-expression)]))

(define (no-op-event name args args^ e)
  (define (contains-remove-event e)
    (match e
      [(remove-constraint-event (oc _ rator rands _ _))
       (and (eq? rator name)
            (andmap eq? args rands)
            e)]
      [(composite-event ls)
       (ormap contains-remove-event ls)]
      [_ #f]))
  (and 
   e
   (andmap eq? args args^)
   (contains-remove-event e)))

(define (default-reify sym . args)
  (define var-free-rands
    (filter-not any/var? args))
  (cond
   [(null? var-free-rands) `()]
   [else `((,sym . ,(sort var-free-rands lex<=)))]))

(define (walk u s [c #f] [e #f])
  (cond
   [e (walk-event u s e)]
   [else (walk-internal u s)]))

(define-constraint-type constraint walk)

(define (walk* u s [c #f] [e #f])
  (let ([v (walk u s c e)])
    (cond
     [(mk-struct? v)
      (define (k a d) 
        ((constructor v)
         (walk* a s)
         (walk* d s)))
      (recur v k)]
     (else v))))

(define (walk-event u s e)
  (cond
   [(and (add-association-event? e)
         (eq? (add-association-event-u e) u))
    (add-association-event-v e)]
   [(and (add-substitution-prefix-event? e)
         (assq u (add-substitution-prefix-event-p e)))
    => cdr]
   [else u]))

(define (enforce x)
  (conj (add-event (enforce-event x)) send-event))

(define (reify x)
  (lambda@ (a [s c q t e])
    (when e (error 'reify "internal error, event not empty ~s" e))
    (define subst (substitution-s s))
    (define store (constraint-store-c c))
    (define v (walk* x subst))
    (define r (reify-s v empty-s))
    (define v^ (reify-term v r))
    (define answer
      (cond
       [(null? r) v^]
       [else (reify-constraints v^ r store)]))
    (choiceg answer empty-f)))

;; reifies the substitution, returning the reified substitution
(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
     [(var? v) 
      `((,v . ,(reify-n v (size-s s))) . ,s)]
     [(mk-struct? v) 
      (define (k a d) 
        (reify-s d (reify-s a s)))
      (recur v k)]
     [else s])))

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

;; sorts a list by lex<=
(define (sort-by-lex<= l) (sort l lex<=))

;; for pretty reification
(define lex<=
  (lambda (x y)
    (cond
      ((vector? x) #t)
      ((vector? y) #f)
      ((port? x) #t)
      ((port? y) #f)
      ((procedure? x) #t)
      ((procedure? y) #f)
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((char? x)
       (cond
         ((char? y) (char<=? x y))
         (else #t)))
      ((char? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
      ((string? x)
       (cond
         ((string? y) (string<=? x y))
         (else #t)))
      ((string? y) #f)
      ((symbol? x)
       (cond
         ((symbol? y)
          (string<=? (symbol->string x)
                     (symbol->string y)))
         (else #t)))
      ((symbol? y) #f)
      ((pair? x)
       (cond
         ((pair? y)
          (cond          
            ((equal? (car x) (car y))
             (lex<= (cdr x) (cdr y)))
            (else (lex<= (car x) (car y)))))))
      ((pair? y) #f)
      (else #t))))

(define (insert-in-lex-order x ls)
  (cond
   [(null? ls) (list x)]
   [(lex<= x (car ls)) (cons x ls)]
   [else (cons (car ls) (insert-in-lex-order x (cdr ls)))]))

(define (run-reify-fns v r store)
  (hash->list
   (for*/fold
    ([h (hasheq)])
    ([(key ocs) store]
     [oc ocs]
     #:when (oc-reify oc))
    (define-values (sym ans)
      ((oc-reify oc) v r))
    #:break (any/var? ans)
    (define updatefn (curry insert-in-lex-order ans))
    (hash-update h sym updatefn '()))))

(define-syntax run/lazy
  (syntax-rules ()
    ((_ (x) g ...) 
     (let ([a-inf ((fresh (x) g ... (enforce x) (reify x)) empty-a)])
       (generator () (take/lazy a-inf))))))

;; convenience macro to integrate Scheme and cKanren, 
;; returns n answers to the goals g0 g1 ... where x is fresh
(define-syntax run
  (syntax-rules ()
    [(_ n (x) g0 g1 ...)
     (let ([stream (run/lazy (x) g0 g1 ...)])
       (take n stream))]
    [(_ n (x ...) g ...)
     (run n (q) (fresh (x ...) (update-s q `(,x ...)) g ...))]))

;; RUNS ALL THE THINGS
(define-syntax run*
  (syntax-rules ()
    [(_ (x ...) g ...) (run #f (x ...) g ...)]))

(define-syntax case/lazy
  (syntax-rules ()
    [(_ gen [() no-answer-clause] [(x g) an-answer-clause])
     (let ([g gen])
       (call-with-values (lambda () (g))
         (case-lambda
          [() no-answer-clause]
          [(x) an-answer-clause])))]))

;; given a number n and a stream, takes n answers from f
(define (take n stream)
  (cond
   [(and n (zero? n)) '()]
   [else
    (case/lazy stream
     [() '()]
     [(a _) (cons a (take (and n (- n 1)) stream))])]))

(define (take/lazy f)
  (case-inf (f)
   [() (yield)]
   [(f) (take/lazy f)]
   [(a) (yield a)]
   [(a f) (begin (yield a) (take/lazy f))]))

(define (prefix-c c c^)
  (for/fold 
   ([prefix '()])
   ([(key ocs^) c^])
   (define ocs (hash-ref c key '()))
   (let prefix-loop ([ocs^ ocs^] [prefix prefix])
     (cond
      [(eq? ocs ocs^) 
       prefix]
      [else
       (prefix-loop (cdr ocs^) (cons (car ocs^) prefix))]))))

;; given a new substitution and constraint store, adds the prefixes of
;; each to the existing substitution and constraint store. the
;; constraints in c-prefix still need to run
(define (update-package s^ c^)
  (lambda@ (a [s c q t e])
    (define s-prefix (prefix-s (substitution-s s) s^))
    (define c-prefix (prefix-c (constraint-store-c c) c^))
    (define e^ (add-substitution-prefix-event s-prefix))
    (define new-e (compose-events e e^))
    (define run-cs
      (lambda@ (a)
        (for/fold ([a-inf a]) ([oc c-prefix])
          (bindm a-inf (oc-proc oc)))))
    (define add-ss
      (lambda@ (a)
        (for/fold ([a-inf a]) ([p s-prefix])
          (bindm a-inf (update-s (car p) (cdr p))))))
    (bindm
     (make-a s c q t new-e)
     (conj run-cs add-ss send-event))))



