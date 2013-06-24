#lang racket/base

(require racket/generic
         "helpers.rkt"
         "infs.rkt"
         "running.rkt")

(require (for-syntax racket/base))

 ;; variables
(provide (struct-out var) define-var-type cvar->str)

;; goals
(provide (struct-out goal) lambdag@ lambdag@/private)

;; == VARIABLES ================================================================

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

;; == GOALS ====================================================================

;; a goal is just a function that can be applied to a's
(struct goal (fn) 
  #:property prop:procedure (struct-field-index fn)
  #:methods gen:custom-write 
  ([define (write-proc goal port mode)
     ((parse-mode mode) "#<goal>" port)]))

;; macro to return a goal with the specified function
(define-syntax lambdag@
  (syntax-rules ()
    [(_ (a) e ...) 
     (lambdag@/private (a) e ...)]
    [(_ (a : s) e ...)
     (lambdag@/private (a) 
       (let ([s (substitution-s (a-s a))])
         e ...))]
    [(_ (a : s c) e ...)
     (lambdag@/private (a) 
       (let ([s (substitution-s (a-s a))]
             [c (constraint-store-c (a-c a))])
         e ...))]))

;; internal macro that can also divide the package into the queue and the tree
(define-syntax lambdag@/private
  (syntax-rules ()
    [(_ (a) e ...)
     (goal (lambda (a) e ...))]
    [(_ (a div s c q t) e ...)
     (lambdag@/private (a)
         (let ([s (a-s a)]
               [c (a-c a)]
               [q (a-q a)] 
               [t (a-t a)])
           e ...))]))

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
(define (walk v s)
  (cond
   ((and (var? v) (assq v s))
    => (lambda (a) (walk (cdr a) s)))
   (else v)))

;; walks a possibly nested structure
(define (walk* w s)
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
  (lambdam@/private (a : s c q t)
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
  (lambdam@/private (a : s c q t)
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
  (lambdam@/private (a : s c q t)
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
    (lambdam@/private (a)
      (let ([c (constraint-store-c (a-c a))])
        ((run-constraints (filter-memq/rator subs c)) a)))))

(define (run-constraint-interactions oc)
  (lambdam@/private (a : s c q t)
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
  (lambdam@/private (a : s c q t)
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
(define empty-q succeed)
(define empty-q? ((curry eq?) empty-q))

(define (ext-q q q^) (conj q q^))

;; DFS: first do the continuation that was already in the store, then
;; do the continuation generated by running that goal, then finally do
;; the input continuation
(define (update-q-dfs new-enforce)
  (lambdam@/private (a : s c q-old t)
    (let ([q-new
           (lambdag@/private (a : s c q-new t)
             ((ext-q q-new new-enforce)
              (make-a s c empty-q t)))])
      (make-a s c (ext-q q-old q-new) t))))

;; this interweaves DFS and BFS somehow
(define (update-q-hybrid new-enforce)
  (lambdam@/private (a : s c q-old t)
    (let ([q-new
           (lambdag@/private (a : s c q-new t)
             ((ext-q new-enforce q-new)
              (make-a s c empty-q t)))])
      (make-a s c (ext-q q-old q-new) t))))

;; BFS: first do the continuation that was already in the store,
;; leaving the continuation it generates in the store while the input
;; continuation runs.
(define (update-q-bfs new-enforce)
  (lambdam@/private (a : s c q-old t)
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
  (lambdam@/private (a : s c q t)
    (define-values (s^ update-s-fn)
      (update-s-prefix (substitution-s s) (constraint-store-c c) (car s^/c^)))
    (define update-c-fn
      (lambdam@/private (a)
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
(define-syntax lambdam@/private
  (syntax-rules (:)
    [(_ (a) e ...)
     (constraint (lambda (a) e ...))]
    [(_ (a : s c q t) e ...)
     (lambdam@/private (a) 
       (let ([s (a-s a)] 
             [c (a-c a)]
             [q (a-q a)]
             [t (a-t a)])
         e ...))]))

(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambdam@/private (a) e ...)]
    [(_ (a : s) e ...)
     (lambdam@/private (a) 
       (let ([s (substitution-s (a-s a))]) 
         e ...))]
    [(_ (a : s c) e ...)
     (lambdam@/private (a) 
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

