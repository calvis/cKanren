#lang racket

(require racket/generic 
         racket/stxparam
         racket/generator
         "src/errors.rkt"
         (only-in rackunit check-equal?))

(require (for-syntax 
          syntax/parse
          racket/syntax
          "src/errors.rkt"))

(provide
 var? define-var-type goal? make-a c->list empty-s empty-c
 update-s update-c any/var?  prefix-s prtm identitym composem
 goal-construct ext-c build-oc oc-rands oc-rator run run* prt
 extend-enforce-fns extend-reify-fns goal? a?  walk walk* oc?
 mzerog unitg onceo fresh-aux conde conda condu ifa ifu project fresh
 succeed fail enforce reify empty-a take mzerom bindm constraint?
 format-source reify-cvar var ext-s gen:mk-struct recur constructor
 mk-struct?  lex<= sort-by-lex<= reify-with-colon default-mk-struct?
 occurs-check run-relevant-constraints build-attr-oc attr-oc?  attr-oc-uw?
 get-attributes filter/rator filter-not/rator default-reify attr-oc-type
 filter-memq/rator define-lazy-goal replace-ocs same-default-type?
 override-occurs-check? update-c-nocheck reify-term var-x ext-c*
 filter-not-memq/rator #%app-safe use-constraints debug replace-s
 update-s-nocheck update-s-prefix attr-tag update-package oc-proc
 default-reify-attr : define-constraint-interaction run-constraints
 run/lazy case/lazy start/interactive resume/interactive reify/interactive 
 enforce/interactive exit/interactive extend-subscriptions conj
 update-args)

(provide
 (rename-out 
  [lambdam@-external lambdam@]
  [lambdag@-external lambdag@]
  [trace-define-mk   trace-define]))

(provide 
 (for-syntax search-strategy))

;; parses the input to a write-proc
(define (parse-mode mode)
  (case mode [(#t) display] [(#f) display] [else display]))

(define attr-tag 'attr)

(define-syntax : (syntax-rules ()))

;; == PARAMETERS ===============================================================

(define ((extend-parameter param) tag fn)
  (let ((fns (param)))
    (and (not (assq tag fns))
         (param (cons `(,tag . ,fn) fns)))))

;; == VARIABLES =================================================================

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(define-generics cvar (cvar->str cvar))

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct var (x) 
  #:methods gen:cvar 
  [(define (cvar->str x) "_")]
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-var args))])

(define-syntax-rule (define-var-type name str rest ...)
  (struct name var () rest ...
    #:methods gen:cvar
    [(define (cvar->str x) str)]
    #:methods gen:custom-write
    [(define (write-proc . args) (apply write-var args))]))

;; write-var controls how variables are displayed
(define (write-var var port mode)
  ((parse-mode mode) (format "#~a(~s)" (cvar->str var) (var-x var)) port))

;; =============================================================================

(struct a-inf ())

(struct mzerof a-inf ())
(struct choiceg a-inf (a f))
(struct inc a-inf (e) #:property prop:procedure (struct-field-index e))

;; macro that delays expressions
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

;; delays an expression
(define-syntax delay
  (syntax-rules ()
    [(_ e) (inc (lambdaf@ () e))]))

(define empty-f (delay (mzerog)))

;; == GOALS ====================================================================

;; a goal is just a function that can be applied to a's
(struct goal (fn) 
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<goal>" port)]))

;; macro to return a goal with the specified function
(define-syntax lambdag@-external
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambdag@ (a) e ...)]
    [(_ (a : s) e ...)
     (lambdag@ (a) 
       (let ([s (substitution-s (a-s a))])
         e ...))]
    [(_ (a : s c) e ...)
     (lambdag@ (a) 
       (let ([s (substitution-s (a-s a))]
             [c (constraint-store-c (a-c a))])
         e ...))]))

;; internal macro that can also divide the package into the queue and the tree
(define-syntax lambdag@
  (syntax-rules (:)
    [(_ (a) e ...)
     (goal (lambda (a) e ...))]
    [(_ (a : s c q t) e ...)
     (lambdag@ (a)
       (let ([s (a-s a)]
             [c (a-c a)]
             [q (a-q a)] 
             [t (a-t a)])
         e ...))]))

;; the failure value
(define (mzerog) (mzerof))

;; the identity goal
(define unitg (lambdag@ (a) a))

;; succeed and fail are the simplest succeeding and failing goals
(define succeed unitg)
(define fail    (lambdag@ (a) (mzerog)))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.

(define prt  
  (lambdag@ (a) (begin (printf "~a\n" a) a)))
(define (prtm . m) 
  (lambdag@ (a) (begin (apply printf m) a)))

(define (prtt . m) 
  (lambdag@ (a : s c q t) 
    (begin (display t) (display " ") (apply printf m) a)))

;; =============================================================================

;; convenience macro for dispatching on the type of a-inf
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ([a-inf e])
       (cond
        [(mzerof? a-inf) e0]
        [(inc? a-inf) (let ([f^ (inc-e a-inf)]) e1)]
        [(a? a-inf) (let ([a^ a-inf]) e2)]
        [(choiceg? a-inf) (let ([a (choiceg-a a-inf)] [f (choiceg-f a-inf)]) e3)]
        [else (error 'case-inf "not an a-inf ~s" e)])))))

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

;; =============================================================================

;; defines a macro to create new unconstrained variables
(define-syntax fresh-aux
  (syntax-rules ()
    [(_ constructor (x ...) g)
     (let ([x (constructor 'x)] ...) g)]
    [(_ constructor (x ...) g0 g1 g* ...)
     (let ([x (constructor 'x)] ...)
       (conj g0 g1 g* ...))]))

;; miniKanren's "fresh" defined in terms of fresh-aux over var
(define-syntax-rule (fresh (x ...) g g* ...)
  (fresh-aux var (x ...) g g* ...))

(define-syntax-rule 
  (conj g g* ...)
  (lambdag@ (a) (delay (bindg* (app-goal g a) g* ...))))

;; performs a conjunction over goals
(define-syntax bindg*
  (syntax-rules ()
    [(_ e) e]
    [(_ e g g* ...)
     (bindg* (bindg e g) g* ...)]))

;; applies a goal to an a-inf
(define bindg
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzerog))
      ((f) (delay (bindg (f) g)))
      ((a) (app-goal g a))
      ((a f) (mplusg (app-goal g a) (delay (bindg (f) g)))))))

(define-syntax mplusg*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...)
     (mplusg e0 (delay (mplusg* e ...))))))

(define mplusg
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (delay (mplusg (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (delay (mplusg (f) f^)))))))

(begin-for-syntax
 (define expand-debug? (make-parameter #f)))

(define-syntax-parameter conde
  (lambda (stx)
    (syntax-parse stx
      [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
       (cond
         [(expand-debug?)
          (with-syntax ([(branches ...) (attribute branch-name)])
            #'(debug-conde [#:name branches g g* ...] ...))]
         [else 
          #'(lambdag@ (a) 
              (delay (mplusg* (bindg* (app-goal g a) g* ...) ...)))])])))

(define-syntax (debug-conde stx)
  (syntax-parse stx
    [(_ ((~optional (~seq #:name branch-name)) g g* ...) ...+)
     (with-syntax ([(labels ...) (attribute branch-name)])
       #'(lambdag@ (a : s c q t) 
           (delay 
            (mplusg* 
             (let ([a (make-a s c q (add-level t 'labels))])
               (bindg* (app-goal g a) g* ...))
             ...))))]))

(define-syntax (debug stx)
  (syntax-parse stx
    [(debug #:on)
     (begin (expand-debug? #t) #'(debug? #t))]
    [(debug #:off)
     (begin (expand-debug? #f) #'(debug? #f))]
    [(debug expr ...+)
     #'(syntax-parameterize 
        ([conde (... (syntax-rules ()
                       ([_ clauses ...]
                        (debug-conde clauses ...))))])
        (parameterize ([debug? #t])
          expr ...))]))

(define-syntax-rule (conda (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (delay (ifa ((app-goal g0 a) g ...) 
                ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (delay (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a-inf g ...)))))))

(define-syntax-rule (condu (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (delay
     (ifu ((app-goal g0 a) g ...)
          ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (delay (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a g ...)))))))

(define-syntax-rule (project (x ...) g g* ...) 
  (lambdag@-external (a : s)
    (let ((x (walk* x s)) ...)
      ((conj g g* ...) a))))

(define onceo (lambda (g) (condu (g))))

(define-syntax (app-goal x)
  (syntax-case x ()
    [(_ g a) #`((wrap-goal g #,(build-srcloc-stx #'g)) a)]))

(define (non-goal-error-msg val)
  (string-append
   "expression evaluated to non-goal where a goal was expected"
   (format "\n  value: ~s" val)))

(define (wrap-goal val src)
  (cond
   [(goal? val) val]
   [(format-source src) => 
    (lambda (loc) (error loc (non-goal-error-msg val)))]
   [else (error (non-goal-error-msg val))]))

;; =============================================================================

(define-generics mk-struct
  ;; recur allows generic traversing of mk-structs.  k should be a
  ;; procedure expecting two arguments, the first thing to process,
  ;; and a list of remaining things to process.
  (recur mk-struct k)

  ;; returns a function that will create a new mk-struct given
  ;; arguments like the arguments to k
  (constructor mk-struct)

  ;; for reification 
  (reify-mk-struct mk-struct r)

  ;; structs also have the option of overriding the occurs-check for
  ;; variables if it's okay to unify a variable to a struct with the
  ;; same variable inside (ex. sets)
  (override-occurs-check? mk-struct)

  #:defaults
  ([pair?
    (define (recur p k)
      (k (car p) (cdr p)))
    (define (constructor p) cons)
    (define (override-occurs-check? p) #f)
    (define (reify-mk-struct p r)
      (reify-pair p r))]
   [vector?
    (define (recur v k)
      (let ([v (vector->list v)])
        (k (car v) (cdr v))))
    (define (constructor v)
      (compose list->vector cons))
    (define (override-occurs-check? v) #f)
    (define (reify-mk-struct v r)
      (reify-vector v r))]))

(define (reify-term t r)
  (cond
   [(mk-struct? t)
    (reify-mk-struct t r)]
   [else (walk t r)]))

(define (default-mk-struct? x)
  (or (pair? x) (vector? x)))

(define (same-default-type? x y)
  (or (and (pair? x) (pair? y))
      (and (vector? x) (vector? y))))

(define (reify-pair p r)
  (cons (reify-term (car p) r)
        (reify-term (cdr p) r)))

(define (reify-vector v r)
  (vector-map (lambda (t) (reify-term t r)) v))

;; == SUBSTITUTIONS ============================================================

;; wraps a substitution
(struct substitution (s)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-substitution args))])

;; writes a substitution
(define (write-substitution substitution port mode)
  (define fn (lambda (s) ((parse-mode mode) s port)))
  (define s (substitution-s substitution))
  (fn "#s[")
  (for ([p s])
    (fn " (") (fn (car p)) (fn " . ") (fn (cdr p)) (fn ")"))
  (unless (null? s) (fn " "))
  (fn "]"))

;; the empty association list, abbreviated s
(define empty-s '())

;; extends a substitution with a binding of x to v
(define (ext-s x v s)
  (cons `(,x . ,v) s))

(define (ext-s* p s)
  (append p s))

;; checks if x appears in v
(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or (occurs-check x (car v) s)
             (occurs-check x (cdr v) s)))
        (else #f)))))

;; returns the size of a substitution
(define size-s
  (lambda (s)
    (length s)))

;; walk an s
(define (walk v s . rest)
  (cond
   ((and (var? v) (assq v s))
    => (lambda (a) (walk (cdr a) s)))
   (else v)))

;; walks a possibly nested structure
(define (walk* w s . rest)
  (let ((v (walk w s)))
    (cond
     ((mk-struct? v)
      (recur v 
       (lambda (a d) 
         ((constructor v)
          (walk* a s)
          (walk* d s)))))
     (else v))))

;; a function that will safely extend the subsitution with
;; a binding of x to v
(define (update-s-check x v)
  (lambdam@ (a : s c q t)
    (let ([s (substitution-s s)]
          [c (constraint-store-c c)])
      (let ((x (walk x s))
            (v (walk v s)))
        (cond
         [(or (var? x) (var? v))
          (update-s-internal x v s c q t)]
         [(equal? x v) a]
         [else #f])))))

;; a function that will insecurely extend the substitution 
;; with a binding of x to v 
(define (update-s-nocheck x v)
  (lambdam@ (a : s c q t)
    (let ([s (substitution-s s)]
          [c (constraint-store-c c)])
      (update-s-internal s c q t))))

(define update-s update-s-check)

;; s and c should be unwrapped
(define (update-s-internal x v s c q t)
  ((run-relevant-constraints (if (var? v) `(,x ,v) `(,x)) c)
   (make-a (substitution (ext-s x v s)) (constraint-store c) q t)))

;; for subsumption checks
(define (replace-s s^)
  (lambdam@ (a : s c q t)
    (make-a (substitution s^) c q t)))

;; returns an updated substitution and a function that will run all
;; the relevant constraints
(define (update-s-prefix s c s^)
  (define p (prefix-s s s^))
  (define relevant-vars (map car p))
  (define run-constraints-fn
    (run-relevant-constraints relevant-vars c))
  (values (ext-s* p s) run-constraints-fn))

;; returns the part of s^ that is a prefix of s
(define (prefix-s s s^)
  (define (loop s^) 
    (cond
     [(eq? s^ s) '()] 
     [else (cons (car s^) (loop (cdr s^)))]))
  (if (null? s) s^ (loop s^)))

;; == CONSTRAINT STORE =========================================================

;; wrapper for a constraint store
(struct constraint-store (c)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-constraint-store args))])

;; writes a constraint store
(define (write-constraint-store constraint-store port mode)
  (define fn (lambda (s) ((parse-mode mode) s port)))
  (define c (constraint-store-c constraint-store))
  (fn "#c[")
  (let ([f (lambda (key ocs) (for ([oc ocs]) (fn " ") (fn oc)))])
    (hash-for-each c f))
  (unless (null? c) (fn " "))
  (fn "]"))

;; an empty constraint store
(define empty-c (hasheq))

;; extends the constraint store c with oc
(define (ext-c oc c) 
  (hash-update c (oc-rator oc) (lambda (ocs) (cons oc ocs)) '()))

(define (ext-c* ocs c)
  (for/fold ([c c]) ([oc ocs]) (ext-c oc c)))

;; checks if oc is in c
(define (memq-c oc c)
  (let ([ocs (filter/rator (oc-rator oc) c)])
    (memq oc ocs)))

;; removes oc from c
(define (remq-c oc c) 
  (hash-update c (oc-rator oc) (lambda (ocs) (remq oc ocs)) '()))

;; removes all ocs in oc* from c
(define (remq*-c oc* c)
  (for/fold ([c c]) ([oc oc*]) (remq-c oc c)))

;; filters the constraint store
(define (filter/rator key c)
  (unless (hash? c)
    (error 'filter/rator "not given a c ~s\n" c))
  (hash-ref c key '()))

(define (filter-not/rator sym c)
  (unless (hash? c)
    (error 'filter-not/rator "not given a c ~s\n" c))
  (apply append (for/list ([key (remq sym (hash-keys c))]) (hash-ref c key '()))))

(define (filter-memq/rator symls c)
  (unless (hash? c)
    (error 'filter-memq/rator "not given a c ~s\n" c))
  (apply append (for/list ([key symls]) (hash-ref c key '()))))

(define (filter-not-memq/rator symls c)
  (unless (hash? c)
    (error 'filter-not-memq/rator "not given a c ~s\n" c))
  (apply append (for/list ([key (hash-keys c)])
                          (cond
                           [(memq key symls) '()]
                           [else (hash-ref c key '())]))))

;; adds oc to the constraint store if it contains a non-ground var
(define (update-c oc)
  (cond
   [(any/var? (oc-rands oc))
    (update-c-nocheck oc)]
   [else identitym]))

(define (update-c-nocheck oc)
  (run-constraint-interactions oc))

;; a parameter containing subscriptions
;; hash maps publisher to a list of subscribers
(define subscriptions (make-parameter (hash)))

;; extends the subscriptions of all publishers in pubs with sub
(define (extend-subscriptions sub pubs)
  (subscriptions
   (for/fold
    ([subs (subscriptions)])
    ([pub pubs])
    (define (update-fn other-subs)
      (cond
       [(memq sub other-subs) other-subs]
       [else (cons sub other-subs)]))
    (hash-update subs pub update-fn '()))))

(define (get-subscribers oc)
  (let ([subs (subscriptions)])
    (hash-ref subs (oc-rator oc) '())))

(define (run-subscribers oc)
  (let ([subs (get-subscribers oc)])
    (lambdam@ (a)
      (let ([c (constraint-store-c (a-c a))])
        ((run-constraints (filter-memq/rator subs c)) a)))))

(define (run-constraint-interactions oc)
  (lambdam@ (a : s c q t)
    (let ([fns (constraint-interactions)])
      (let loop ([fns fns])
        (cond
         [(null? fns) 
          (let ([old-c (constraint-store-c c)])
            (let ([new-store (constraint-store (ext-c oc old-c))])
              (make-a s new-store q t)
              #;((run-subscribers oc) (make-a s new-store q t))
              ))]
         [(((cdar fns) oc) a)]
         [else (loop (cdr fns))])))))

;; replaces all ocs with a rator equal to key with ocs^
(define (replace-ocs key ocs^)
  (lambdam@ (a : s c q t)
    (let* ([old-store (constraint-store-c c)]
           [new-c (hash-update old-store key (lambda (ocs) ocs^) '())]
           [new-store (constraint-store new-c)])
      (make-a s new-store q t))))

(define (run-c-prefix c c^)
  (for/fold 
   ([fn identitym])
   ([(key ocs^) c^])
   (define ocs (hash-ref c key '()))
   (let loop ([ocs^ ocs^])
     (cond
      [(eq? ocs ocs^) fn]
      [else
       (composem 
        (loop (cdr ocs^))
        (oc-proc (car ocs^)))]))))

(define (c->list c)
  (apply append (hash-values c)))

;; == QUEUE ====================================================================

;; an empty queue 
(define empty-q unitg)
(define empty-q? ((curry eq?) empty-q))

(define (ext-q q q^) (conj q q^))

;; DFS: first do the continuation that was already in the store, then
;; do the continuation generated by running that goal, then finally do
;; the input continuation
(define (update-q-dfs new-enforce)
  (lambdam@ (a : s c q-old t)
    (let ([q-new
           (lambdag@ (a : s c q-new t)
             ((ext-q q-new new-enforce)
              (make-a s c empty-q t)))])
      (make-a s c (ext-q q-old q-new) t))))

;; this interweaves DFS and BFS somehow
(define (update-q-hybrid new-enforce)
  (lambdam@ (a : s c q-old t)
    (let ([q-new
           (lambdag@ (a : s c q-new t)
             ((ext-q new-enforce q-new)
              (make-a s c empty-q t)))])
      (make-a s c (ext-q q-old q-new) t))))

;; BFS: first do the continuation that was already in the store,
;; leaving the continuation it generates in the store while the input
;; continuation runs.
(define (update-q-bfs new-enforce)
  (lambdam@ (a : s c q-old t)
    (make-a s c (ext-q q-old new-enforce) t)))

;; == TREE =====================================================================

;; wrapper for the tree
(struct path (t)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-path args))])

;; writes a path
(define (write-path path port mode)
  (let ([fn (lambda (s) ((parse-mode mode) s port))])
    (fn "#path[" )
    (unless (null? (path-t path)) (fn " "))
    (for ([br (reverse (path-t path))])
         (fn (format "~s " br)))
    (fn "]")))

;; an empty tree
(define empty-t (path '()))

;; adds a level to the tree with label l if it exists, a gensym otherwise
(define (add-level p l) 
  (cond
   [l (path (cons l (path-t p)))]
   [else (path (cons (gensym 'tr) (path-t p)))]))

;; == PACKAGE ==================================================================

;; a package is a structure containing a substitution and
;; a constraint store
(struct a a-inf (s c q t)
  #:extra-constructor-name make-a
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-package args))])

;; when debug?ging is turned on, print out the path as well
(define debug? (make-parameter #f))

;; controls how packages are displayed
(define (write-package a port mode)
  (let ([fn (lambda (s) ((parse-mode mode) s port))])
    (if (debug?)
        (fn (format "#a{ ~s ~a ~a }" (a-t a) (a-s a) (a-c a)))
        (fn (format "#a{ ~a ~a }" (a-s a) (a-c a))))))

;; the empty package
(define empty-a 
  (make-a (substitution empty-s)
          (constraint-store empty-c)
          empty-q
          empty-t))

;; should update the substitution with the bindings in s^, then run
;; all the constraints in c^, then run all the constraints relating to
;; the variables in s^
(define (update-package s^/c^)
  (lambdam@ (a : s c q t)
    (define-values (s^ update-s-fn)
      (update-s-prefix (substitution-s s) (constraint-store-c c) (car s^/c^)))
    (define update-c-fn
      (lambdam@ (a)
        ((run-c-prefix (constraint-store-c c) (cdr s^/c^))
         (make-a (substitution s^) c q t))))
    (bindm a (composem update-c-fn update-s-fn))))

;; == CONSTRAINTS ==============================================================

(struct constraint (fn)
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<constraint>" port)]))

;; special lambda for defining constraints
(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) e ...)
     (constraint (lambda (a) e ...))]
    [(_ (a : s c q t) e ...)
     (lambdam@ (a) 
       (let ([s (a-s a)] 
             [c (a-c a)]
             [q (a-q a)]
             [t (a-t a)])
         e ...))]))

(define-syntax lambdam@-external
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambdam@ (a) e ...)]
    [(_ (a : s) e ...)
     (lambdam@ (a) 
       (let ([s (substitution-s (a-s a))]) 
         e ...))]
    [(_ (a : s c) e ...)
     (lambdam@ (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
         e ...))]))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; the simplest failing constraint
(define mzerom (lambdam@ (a) #f))

;; applies a constraint to a package
(define (bindm a fm) (fm a))

;; composes two constraints together
(define (composem . fm*)
  (lambdam@ (a)
    (cond
     [(null? fm*) a]
     [((car fm*) a)
      => (apply composem (cdr fm*))]
     [else #f])))

;; constructs a goal from a constraint
(define (goal-construct fm)
  (lambdag@ (a) (or (fm a) (mzerog))))

;; the representation of a constraint in the constraint store 
;; contains a closure waiting to be evaluated with a new package,
;; a symbolic representation of the constrant's name and it's args
(struct oc (proc rator rands) 
  #:extra-constructor-name make-oc
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-oc args))])

;; displays an oc
(define (write-oc oc port mode)
  (define fn (lambda (str) ((parse-mode mode) str port)))
  (fn (format "#oc<~a" (oc-rator oc)))
  (for ([arg (oc-rands oc)])
    (fn (format " ~a" arg)))
  (fn (format ">")))

;; creates an oc given the constraint operation and it's args
(define-syntax (build-oc x)
  (syntax-case x ()
    ((_ op arg ...)
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       #'(let ((arg^ arg) ...)
           (make-oc (op arg^ ...) 'op `(,arg^ ...)))))))

;; defines an attributed constraint (for attributed variables)
(struct attr-oc oc (type uw?) ;; for "unifies with?"
  #:extra-constructor-name make-attr-oc
  #:methods gen:custom-write
  [(define (write-proc attr-oc port mode)
     (define fn (lambda (str) ((parse-mode mode) str port)))
     (fn (format "#oc<~a ~s" (oc-rator attr-oc) (attr-oc-type attr-oc)))
     (for ([arg (oc-rands attr-oc)])
          (fn (format " ~a" arg)))
     (fn (format ">")))])

;; builds an attributed constraint
(define-syntax build-attr-oc
  (syntax-rules ()
    [(_ op x uw?)
     (let ((x^ x))
       (make-attr-oc (op x^) attr-tag `(,x^) 'op uw?))]))

;; gets the attributes of variable x in the constraint store
(define (get-attributes x c)
  (define (x-attr? oc) 
    (eq? (car (oc-rands oc)) x))
  (let ((attrs (filter x-attr? (filter/rator attr-tag c))))
    (and (not (null? attrs)) attrs)))

;; == FIXPOINT =================================================================

;; fixed point algorithm given some variables x* that have changed,
;; and list of constraints c.  will rerun any constraints in c that
;; mention x*
(define (run-constraints c)
  (cond
   [(hash? c)
    (for/fold 
     ([rest identitym])
     ([(key ocs) c])
     (composem 
      (for/fold 
       ([fn identitym])
       ([oc ocs])
       (composem fn (rem/run oc)))
      rest))]
   [(list? c)
    (for/fold 
     ([rest identitym])
     ([oc c])
     (composem rest (rem/run oc)))]
   [else (error 'run-constraints "don't know how to run ~s" c)]))

(define (run-relevant-constraints x* c)
  (for/fold 
   ([rest identitym])
   ([(key ocs) c])
   (composem 
    (for/fold 
     ([fn identitym])
     ([oc ocs]
      #:when (any-relevant/var? (oc-rands oc) x*))
     (composem fn (rem/run oc)))
    rest)))

;; removes a constraint from the constraint store and then 
;; reruns it as if it was just being introduced (will add itself
;; back to the constraint store if it still is waiting on info)
(define (rem/run oc)
  (lambdam@ (a : s c q t)
    (let ([ocs (constraint-store-c c)])
      (cond
       [(memq-c oc ocs)
        ((oc-proc oc)
         (let ([new-c (constraint-store (remq-c oc ocs))])
           (make-a s new-c q t)))]
       (else a)))))

;; == ENFORCE CONSTRAINTS ======================================================

;; a list of functions to be run during enforce
(define enforce-fns (make-parameter '()))
(define extend-enforce-fns (extend-parameter enforce-fns))

;; runs all the enforce-constraint functions in enforce-fns
;; and all the fixpoint-enforce-fns in fixpoint-enforce-fns.. to a fixpoint
(define (enforce x)
  (for/fold
   ([f fixpoint-enforce])
   ([fn (map cdr (enforce-fns))])
   (conj f (fn x))))

(define-for-syntax search-strategy (make-parameter 'hybrid))

;; runs the given search strategy on the queue of lazy goals
(define fixpoint-enforce
  (lambdag@ (a : s c q t)
    (cond
     [(empty-q? q) a]
     [else 
      ((ext-q q fixpoint-enforce) 
       (make-a s c empty-q t))])))

;; useful for printing out information during debugging, not exported atm
;; convenience macro for defining lazy goals
(define-syntax (define-lazy-goal stx)
  (syntax-parse stx
    [(define-lazy-goal (name args ...) body)
     (define (bad-search-strat-error st)
       (error 'define-lazy-goal "unknown search strategy ~s" st))
     (let ([st (search-strategy)])
       (with-syntax 
         ([update-q
           (case st
             [(dfs) #'update-q-dfs]
             [(bfs) #'update-q-bfs]
             [(hybrid) #'update-q-hybrid]
             [else (bad-search-strat-error st)])])
         #`(define (name args ...)
             (goal-construct (update-q body)))))]
    [(define-lazy-goal name (lambda (args ...) body))
     #'(define-lazy-goal (name args ...) body)]))

;; == REIFICATION ==============================================================

;; a list of functions to be run during reification
(define reify-fns        (make-parameter '()))
(define extend-reify-fns (extend-parameter reify-fns))

;; defines whether the constraint store should be printed out
;; with a : inbetween the answer and the constraints on the answer
(define reify-with-colon (make-parameter #t))

;; reifies the constraint store with respect to x
(define (reify x)
  (lambdag@ (a : s c q t)
    (let ([s (substitution-s s)]
          [c (constraint-store-c c)])
      (define v (walk* x s))
      (define r (reify-s v empty-s))
      (define v^ (reify-term v r))
      (define answer
        (cond
         [(null? r) v^]
         [else (reify-constraints v^ r c)]))
      (choiceg answer empty-f))))

;; reifies a cvar
(define (reify-cvar cvar r) (walk cvar r))

;; reifies the substitution, returning the reified substitution
(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
     [(var? v) 
      `((,v . ,(reify-n v (size-s s))) . ,s)]
     [(mk-struct? v) 
      (let ([k (lambda (a d) (reify-s d (reify-s a s)))])
        (recur v k))]
     [else s])))

;; creates a reified symbol
(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar->str cvar) (number->string n))))

;; reifies the constraint store by running all the reification fns
(define (reify-constraints v r ocs)
  (cond
    ((null? ocs) v)
    (else
     (let ((ocs^ (run-reify-fns v r ocs)))
       (cond
        [(null? ocs^) v] 
        [(reify-with-colon) `(,v : . ,(sort-store ocs^))]
        [else `(,v . ,(sort-store ocs^))])))))

;; runs all the reification functions
(define (run-reify-fns v r ocs)
  (for/fold ([ocs^ `()])
            ([fn (map cdr (reify-fns))])
    (append (fn v r ocs) ocs^)))

;; defines a "default" reify function
(define ((default-reify sym cs fn) v r ocs)
  (let ((ocs (filter-memq/rator cs ocs)))
    (let ((rands (filter-not any/var? (walk* (fn (map oc-rands ocs) r) r))))
      (cond
       ((null? rands) `())
       (else `((,sym . ,(sort rands lex<=))))))))

(define ((default-reify-attr sym type fn) v r ocs)
  (let ((ocs (filter (lambda (oc) (eq? (attr-oc-type oc) type))
                     (filter/rator attr-tag ocs))))
    (let ((rands (filter-not any/var? (walk* (fn (map (compose car oc-rands) ocs) r) r))))
      (cond
       ((null? rands) `())
       (else `((,sym . ,(sort rands lex<=))))))))

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

;; == INTEGRATION ==============================================================

(define-syntax run/lazy
  (syntax-rules ()
    ((_ (x) g ...) 
     (let ([a-inf (bindg empty-a (fresh (x) g ... (enforce x) (reify x)))])
       (generator () (take/lazy a-inf))))))

;; convenience macro to integrate Scheme and cKanren, 
;; returns n answers to the goals g0 g1 ... where x is fresh
(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g1 ...)
     (let ([stream (run/lazy (x) g0 g1 ...)])
       (take n stream)))))

;; RUNS ALL THE THINGS
(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(struct running (x a-inf)
  #:methods gen:custom-write 
  [(define (write-proc ra port mode) 
     ((parse-mode mode) "#<running/interactive>" port))])

(struct enforced running ()
  #:methods gen:custom-write 
  [(define (write-proc ra port mode) 
     ((parse-mode mode) "#<running/interactive>" port))])

(define-syntax (start/interactive stx)
  (syntax-parse stx
    [(_ (~seq #:var x) g ...)
     #'(running x (bindg empty-a (conj succeed g ...)))]))

(define-syntax-rule 
  (resume/interactive state g ...)
  (let ([st state])
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (running x (bindg a-inf (conj succeed g ...))))))

(define-syntax-rule 
  (enforce/interactive state)
  (let ([st state])
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (enforced x (bindg a-inf (enforce x))))))

(define-syntax-rule
  (reify/interactive state)
  (let ([st state])
    (unless (enforced? st)
      (error 'reify/interactive "trying to reify an unenforced state ~s" st))
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (bindg a-inf (reify x)))))

(define-syntax-rule 
  (exit/interactive n state)
  (let ([stream
         (generator 
          ()
          (take/lazy
           (let ([st state])
             (reify/interactive
              (cond
               [(enforced? st) state]
               [else (enforce/interactive state)])))))])
    (take n stream)))

(define-syntax-rule
  (exit*/interactive state)
  (exit/interactive #f state))

;; == HELPERS ==================================================================

;; returns #t if p contains any variables
(define (any/var? x)
  (cond
   ((mk-struct? x)
    (recur x (lambda (a d) (or (any/var? a) (any/var? d)))))
   (else (var? x))))

;; returns #t if t constains variables in x*
(define (any-relevant/var? t x*)
  (cond
   ((mk-struct? t)
    (recur t (lambda (a d) (or (any-relevant/var? a x*)
                               (any-relevant/var? d x*)))))
   (else (and (var? t) (memq t x*)))))

;; This is a tracing macro, akin to trace-define in Chez Scheme.  Upon
;; entry to the goal, all arguments to the function will be projected
;; in the current substitution and printed out.
(define-syntax trace-define-mk
  (syntax-rules ()
    ((_ (name a* ...) body)
     (trace-define-mk name (lambda (a* ...) body)))
    ((_ name (lambda (a* ...) body))
     (define name
       (lambda (a* ...)
         (conj
           (project (a* ...)
             (begin
               (display (list 'name a* ...))
               (newline)
               succeed))
           body))))))

;; Should be able to think of importing constraint files as using
;; constraints, not as requiring files.  Abstractiiooonnnnn.
(define-syntax-rule (use-constraints file ...) 
  (require file ...))

(define gensym
  (let ([counter 0])
    (lambda ([x 'g])
      (if (number? x)
          (set! counter x)
          (begin0 (string->unreadable-symbol
                   (format "~a~a" x counter))
                  (set! counter (add1 counter)))))))

;; =============================================================================

;; This is a version of application that will catch when users have
;; misplaced goals.

;; If the user is trying to apply a goal to something that is not a
;; package, or trying to apply a goal to zero or many things, they
;; will get an goal-as-fn-exn.  This will fix the stupid "incorrect
;; number of arguments to #<procedure>" errors.

(struct exn:goal-as-fn exn:fail ())
(define (raise-goal-as-fn-exn src)
  (raise
   (exn:goal-as-fn
    (format "~s: goal applied as a procedure" (format-source src))
    (current-continuation-marks))))

;; The only correct application of a goal g is to a package a; i.e. (g a).
(define-for-syntax (valid-app?-pred fn args) 
  (syntax-case args ()
    [(a) #`(or (not (goal? #,fn)) (a? a))]
    [(a* ...) #`(not (goal? #,fn))]))

(define-syntax (#%app-safe x)
  (syntax-case x () 
    [(_ fn arg ...)
     (with-syntax* ([(fn^ arg^ ...) 
                     (generate-temporaries #'(fn arg ...))]
                    [src (build-srcloc-stx #'fn)]
                    [valid-app? (valid-app?-pred #'fn^ #'(arg^ ...))])
       (syntax/loc x
        (let ([fn^ fn])
          (let ([arg^ arg] ...)
            (cond
             [valid-app? (#%app fn^ arg^ ...)]
             [else (raise-goal-as-fn-exn src)])))))]))


;; CHR

(define constraint-interactions
  (make-parameter '()))

(define extend-constraint-interactions
  (extend-parameter constraint-interactions))

(define-syntax (define-constraint-interaction stx)
  (syntax-parse stx 
    [(define-constraint-interaction 
       name:id
       (constraint-exprs ...)
       (~or (~optional (~seq #:package (a:id : s:id c:id))))
       ...
       clauses ...)
     (define a-name (or (attribute a) (generate-temporary #'?a)))
     (define s-name (or (attribute s) (generate-temporary #'?s)))
     (define c-name (or (attribute c) (generate-temporary #'?c)))
     (with-syntax*
       ([(a s c) (list a-name s-name c-name)]
        [constraint-interaction-expr
         #`(parse-constraint-interaction
            name (constraint-exprs ...) (clauses ...)
            (a s c))])
       #'(extend-constraint-interactions
          'name constraint-interaction-expr))]))

(define-syntax (parse-constraint-interaction stx)
  (syntax-parse stx
    [(parse-constraint-interaction 
      name
      ((rator rands ...) ...)
      ([pred? (constraints ...)] ...)
      (a s c))
     (with-syntax 
       ([(arg ...) (generate-temporaries #'(rator ...))])
       #`(let ()
           (define (run-interaction . arg*)
             (lambdam@ (a : ?s ?c ?q ?t)
               (let ([s (substitution-s ?s)]
                     [c (constraint-store-c ?c)])
                 (match (map oc-rands arg*)
                   [`((rands ...) ...)
                    (cond
                     [pred? 
                      (let ([new-c (remq*-c arg* c)])
                        (let ([new-a (make-a ?s (constraint-store new-c) ?q ?t)])
                          ((composem constraints ...) new-a)))]
                     ...
                     [else #f])]
                   ;; when the rators are all correct but the pattern
                   ;; is more strict than we were expecting, we should
                   ;; fail instead of erroring
                   [_ #f]))))
           (define (name oc)
             (let ([this-rator (oc-rator oc)])
               (lambdam@-external (a : s c)
                 (generate-cond run-interaction (a s c) oc this-rator 
                                () ((rator rands ...) ...)))))
           name))]))

(define-syntax (generate-cond stx)
  (syntax-parse stx 
    [(generate-cond run-interaction (a s c) oc this-rator (pattern ...) ()) #'#f]
    [(generate-cond 
      run-interaction (a s c) oc this-rator
      ((rator-pre rand-pre ...) ...)
      ((rator rand ...) (rator-post rand-post ...) ...))
     (with-syntax
      ([(pre ...)  (generate-temporaries #'(rator-pre ...))]
       [(post ...) (generate-temporaries #'(rator-post ...))]
       [(pre-ocs ...)  #'((filter/rator 'rator-pre c) ...)]
       [(post-ocs ...) #'((filter/rator 'rator-post c) ...)]
       [pattern-applies? #'(eq? 'rator this-rator)])
      (with-syntax
        ([run-rule
          #'(bindm a
              (for*/fold
               ([fn mzerom])
               ([pre    pre-ocs] ...
                [this (list oc)]
                [post  post-ocs] ...)
               (lambdam@-external 
                (a : s c)
                (cond
                 [((run-interaction pre ... this post ...) a)]
                 [else (fn a)]))))]
         [rest-formatted 
          #'(generate-cond 
             run-interaction (a s c) oc this-rator
             ((rator-pre rand-pre ...) ... (rator rand ...))
             ((rator-post rand-post ...) ...))])
        #'(or (and pattern-applies? run-rule) rest-formatted)))]))

;; =============================================================================

(define-syntax (update-args stx)
  (syntax-parse stx
    [(update-args 
      (~seq #:with-args (args ...))
      ([x:id function:expr] ...)
      bodies ...)
     #'(let ([args^ (list args ...)])
         (let ([x (apply function x args^)] ...) 
           bodies ...))]))

