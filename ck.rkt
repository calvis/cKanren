#lang racket

(require racket/generic 
         (for-syntax syntax/parse racket/syntax)) 

(provide
 ;; framework for defining constraints
 update-s update-c any/var? prefix-s prtm
 lambdam@ identitym composem goal-construct ext-c
 build-oc oc-proc oc-rands oc-rator run run* prt
 extend-enforce-fns extend-reify-fns goal? a? 
 walk walk* var? lambdag@ mzerog unitg onceo fresh-aux
 conde conda condu ifa ifu project fresh succeed fail
 lambdaf@ inc enforce-constraints reify empty-a take
 format-source define-cvar-type reify-cvar var ext-s
 gen:mk-struct recur constructor mk-struct? unifiable?
 lex<= sort-by-lex<= reify-with-colon occurs-check
 run-constraints build-attr-oc attr-oc? attr-oc-uw?
 get-attributes filter/rator filter-not/rator default-reify
 extend-fixpoint-enforce-fns filter-memq/rator
 define-lazy-goal trace-define replace-c search-strategy
 (for-syntax build-srcloc))

(define-syntax trace-define
  (syntax-rules ()
    [(_ (name a* ...) body)
     (trace-define name (lambda (a* ...) body))]
    [(_ name (λ (a* ...) body))
     (define name
       (λ (a* ...)
          (fresh ()
            (project (a* ...)
              (begin
                (display (list 'name a* ...))
                (newline)
                succeed))
            body)))]))

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

(define-syntax-rule (define-cvar-type name str)
  (struct name var ()
    #:methods gen:cvar
    [(define (cvar->str x) str)]
    #:methods gen:custom-write
    [(define (write-proc . args) (apply write-var args))]))

;; write-var controls how variables are displayed
(define (write-var var port mode)
  ((parse-mode mode) (format "#~a(~s)" (cvar->str var) (var-x var)) port))

(define (parse-mode mode)
  (case mode [(#t) display] [(#f) display] [else display]))

;; == GOALS ====================================================================

;; a goal is just a function that can be applied to a's
(struct goal (fn) #:property prop:procedure (struct-field-index fn))

;; macro to return a goal with the specified function
(define-syntax lambdag@
  (syntax-rules (:)
    [(_ (a : s c q) e ...)
     (lambdag@ (a) 
       (let ([s (substitution-s (a-s a))]
             [c (constraint-store-c (a-c a))]
             [q (a-q a)])
         e ...))]
    [(_ (a : s c) e ...)
     (lambdag@ (a) 
       (let ([s (substitution-s (a-s a))]
             [c (constraint-store-c (a-c a))])
         e ...))]
    [(_ (a) e ...) 
     (goal (lambda (a) e ...))]))

;; the failure value
(define (mzerog) #f)

;; the identity goal
(define unitg (lambdag@ (a) a))

;; succeed and fail are the simplest succeeding and failing goals
(define succeed unitg)
(define fail    (lambdag@ (a) (mzerog)))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.
(define prt  (lambdag@ (a) (begin (printf "~a\n" a) a)))
(define prtm (lambda m (lambdag@ (a) (begin (apply printf m) a))))

;; =============================================================================

;; macro that delays expressions
(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

;; delays an expression
(define-syntax inc 
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

;; =============================================================================

;; convenience macro for dispatching on the type of a-inf
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf)  (let ((f^ a-inf)) e1))
         ((not (and (pair? a-inf)
                    (procedure? (cdr a-inf))))
          (let ((a^ a-inf)) e2))
         (else (let ((a (car a-inf)) (f (cdr a-inf))) 
                 e3)))))))

(define empty-f (lambdaf@ () (mzerog)))
(define choiceg cons)

;; given a number n and a thunk containing an infinite stream f, takes
;; n answers from f
(define (take n f)
  (cond
    ((and n (zero? n)) '())
    (else
     (case-inf (f)
       (() '())
       ((f) (take n f))
       ((a) (cons a '()))
       ((a f) (cons a (take (and n (- n 1)) f)))))))

;; =============================================================================

(define-syntax-rule (fresh-aux constructor (x ...) g g* ...)
  (lambdag@ (a) 
    (inc 
     (let ((x (constructor (gensym 'x))) ...) 
       (bindg* (app-goal g a) g* ...)))))

(define-syntax-rule (fresh (x ...) g g* ...)
  (fresh-aux var (x ...) g g* ...))

(define-syntax bindg*
  (syntax-rules ()
    [(_ e) e]
    [(_ e g g* ...)
     (bindg* (bindg e g) g* ...)]))

(define bindg
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzerog))
      ((f) (inc (bindg (f) g)))
      ((a) (app-goal g a))
      ((a f) (mplusg (app-goal g a) (lambdaf@ () (bindg (f) g)))))))

(define-syntax mplusg*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...)
     (mplusg e0 (lambdaf@ () (mplusg* e ...))))))

(define mplusg
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (inc (mplusg (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (lambdaf@ () (mplusg (f) f^)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a) 
       (inc 
        (mplusg* 
         (bindg* (app-goal g0 a) g ...)
         (bindg* (app-goal g1 a) g^ ...)
         ...))))))

(define-syntax-rule (conda (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (inc (ifa ((app-goal g0 a) g ...) 
              ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a-inf g ...)))))))

(define-syntax-rule (condu (g0 g ...) (g1 g^ ...) ...)
  (lambdag@ (a)
    (inc
     (ifu ((app-goal g0 a) g ...)
          ((app-goal g1 a) g^ ...) ...))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a g ...)))))))

(define-syntax-rule (project (x ...) g g* ...) 
  (lambdag@ (a : s c)
    (let ((x (walk* x s)) ...)
      ((fresh () g g* ...) a))))

(define onceo (lambda (g) (condu (g))))

;; == ERROR CHECKING ===========================================================

(define-for-syntax (build-srcloc stx)
  #`(srcloc
     '#,(syntax-source stx)
     '#,(syntax-line stx)
     '#,(syntax-column stx)
     '#,(syntax-position stx)
     '#,(syntax-span stx)))

(define-syntax (app-goal x)
  (syntax-case x ()
    [(_ g a) #`((wrap-goal g #,(build-srcloc #'g)) a)]))

(define cd (current-directory))

(define (format-source src)
  (define source (srcloc-source src))
  (cond
   [(path? source)
    (define absolute-path (path->string source))
    (define location (find-relative-path cd absolute-path))
    (define line (srcloc-line src))
    (define column (srcloc-column src))
    (string->symbol (format "~a:~s:~s" location line column))]
   [else #f]))

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
  ;; recur allows generic traversing of mk-structs (for example,
  ;; this is used during unification).  k should be a procedure
  ;; expecting two arguments, the first thing to process, and a 
  ;; list of remaining things to process.  
  (recur mk-struct k)

  ;; returns a function that will create a new mk-struct given
  ;; arguments like the arguments to k
  (constructor mk-struct)

  ;; determines whether mk-struct can unify with x
  (unifiable? mk-struct x)

  ;; for reification 
  (mk-struct->sexp mk-struct)

  #:defaults
  ([pair?
    (define (recur p k)
      (k (car p) (cdr p)))
    (define (constructor p) cons)
    (define (unifiable? p x) (pair? x))
    (define (mk-struct->sexp v) v)]
   [vector?
    (define (recur v k)
      (let ([v (vector->list v)])
        (k (car v) (cdr v))))
    (define (constructor v)
      (compose list->vector cons))
    (define (unifiable? v x) (vector? x))
    (define (mk-struct->sexp v) v)]))

;; == SUBSTITUTIONS ============================================================

(struct substitution (s)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-substitution args))])

(define (write-substitution substitution port mode)
  (define fn (parse-mode mode))
  (define subst-as-str (format-als (substitution-s substitution)))
  (fn subst-as-str port))

(define (format-als s)
  (define (p->str p) 
    (format "(~a . ~a)" (car p) (cdr p)))
  (map p->str s))

;; the empty association list, abbreviated s
(define empty-s '())

;; extends a substitution with a binding of x to v
(define (ext-s x v s)
  (cons `(,x . ,v) s))

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
  (lambdam@ (a : s c q)
    (let ((x (walk x s))
          (v (walk v s)))
      (cond
       ((or (var? x) (var? v))
        ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
         (make-a (ext-s x v s) c q)))
       ((equal? x v) a)
       (else #f)))))

;; a function that will insecurely extend the substitution 
;; with a binding of x to v 
(define (update-s-nocheck x v)
  (lambdam@ (a : s c q)
    ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
     (make-a (ext-s x v s) c q))))

(define update-s update-s-check)

;; == CONSTRAINT STORE =========================================================

(struct constraint-store (c)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-constraint-store args))])

;; an empty constraint store
(define empty-c '())

;; extends the constraint store c with oc
(define (ext-c oc c) (cons oc c))
(define (remq-c oc c) (remq oc c))

(define (write-constraint-store constraint-store port mode)
  ((parse-mode mode) (format "#c<~a>" (constraint-store-c constraint-store)) port))

(define (filter/rator sym c)
  (filter (lambda (oc) (eq? (oc-rator oc) sym)) c))

(define (filter-not/rator sym c)
  (filter (lambda (oc) (not (eq? (oc-rator oc) sym))) c))

(define (filter-memq/rator symls c)
  (filter (lambda (oc) (and (memq (oc-rator oc) symls) #t)) c))

(define (filter-not-memq/rator symls c)
  (filter (lambda (oc) (not (memq (oc-rator oc) symls))) c))

;; adds oc to the constraint store if it contains a non-ground var
(define update-c
  (lambda (oc)
    (lambdam@ (a : s c q)
      (cond
       ((lazy-goal-oc? oc)
        (make-a s c (ext-q oc q)))
       ((any/var? (oc-rands oc))
        (make-a s (ext-c oc c) q))
       (else a)))))

(define (replace-c c^)
  (lambdam@ (a : s c q)
    (make-a s c^ q)))

;; == QUEUE ====================================================================

(require (prefix-in fq: "functional-queue.rkt"))
(define empty-q (fq:make-queue))
(define empty-q? fq:queue-empty?)
(define (ext-q x q) (fq:enqueue q x))
(define de-q fq:dequeue)
(define append-q fq:queue-append)

;; == PACKAGE ==================================================================

;; a package is a structure containing a substitution and
;; a constraint store
(struct a (s c q) 
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-package args))])

(define (make-a s c q)
  (a (substitution s) (constraint-store c) q))

;; the empty package
(define empty-a (make-a empty-s empty-c empty-q))

;; controls how packages are displayed
(define (write-package a port mode)
  ((parse-mode mode)
   (format "(~a . ~a)" (a-s a) (a-c a)) port))

;; == CONSTRAINTS ==============================================================

;; special lambda for defining constraints
(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambda (a) e ...)]
    [(_ (a : s c) e ...)
     (lambdam@ (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
         e ...))]
    [(_ (a : s c q) e ...)
     (lambdam@ (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]
             [q (a-q a)]) 
         e ...))]))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; composes two constraints together
(define (composem fm f^m)
  (lambdam@ (a)
    (cond
     [(fm a) => 
      (lambda (a^) (f^m a^))]
     [else #f])))

;; constructs a goal from a constraint
(define-syntax-rule (goal-construct fm)
  (lambdag@ (a) (fm a)))

;; the representation of a constraint in the constraint store 
;; contains a closure waiting to be evaluated with a new package,
;; a symbolic representation of the constrant's name and it's args
(struct oc (proc rator rands) 
  #:extra-constructor-name make-oc
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-oc args))])

(define (write-oc oc port mode)
  (define fn (lambda (str) ((parse-mode mode) str port)))
  (fn (format "(~a" (oc-rator oc)))
  (for ([arg (oc-rands oc)])
    (fn (format " ~a" arg)))
  (fn (format ")")))

;; creates an oc given the constraint operation and it's args
(define-syntax (build-oc x)
  (syntax-case x ()
    ((_ op arg ...)
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       #'(let ((arg^ arg) ...)
           (make-oc (op arg^ ...) 'op `(,arg^ ...)))))))

(struct attr-oc oc (uw?) ;; for "unifies with?"
  #:extra-constructor-name make-attr-oc)

(define-syntax build-attr-oc
  (syntax-rules ()
    ((_ op x uw?)
     (let ((x^ x))
       (make-attr-oc (op x^) 'op `(,x^) uw?)))))

(define (get-attributes x ocs)
  (define (x-attr-oc? oc) 
    (and (attr-oc? oc) (eq? (car (oc-rands oc)) x)))
  (let ((attrs (filter x-attr-oc? ocs)))
    (and (not (null? attrs)) attrs)))

(struct lazy-goal-oc oc ()
  #:extra-constructor-name make-lazy-goal-oc)

(define-syntax (build-lazy-goal-oc x)
  (syntax-case x ()
    ((_ op arg ...)
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       #'(let ((arg^ arg) ...)
           (make-lazy-goal-oc (op arg^ ...) 'op `(,arg^ ...)))))))

;; == FIXPOINT =================================================================

;; fixed point algorithm given some variables x* that have changed,
;; and a constraint store c.  will rerun any constraints that 
;; mention x*
(define (run-constraints x* c)
  (for/fold ([rest identitym])
            ([oc c]
             #:when (and (not (lazy-goal-oc? oc))
                         (any-relevant/var? (oc-rands oc) x*)))
    (composem rest (rem/run oc))))

;; removes a constraint from the constraint store and then 
;; reruns it as if it was just being introduced (will add itself
;; back to the constraint store if it still is waiting on info)
(define (rem/run oc)
  (lambdam@ (a : s c q)
    (cond
     ((memq oc c)
      ((oc-proc oc)
       (make-a s (remq-c oc c) q)))
     (else a))))

;; == PARAMETERS ===============================================================

(define ((extend-parameter param) tag fn)
  (let ((fns (param)))
    (and (not (assq tag fns))
         (param (cons `(,tag . ,fn) fns)))))

;; == ENFORCE CONSTRAINTS ======================================================

;; a list of functions to be run during enforce-constraints
(define enforce-fns (make-parameter '()))
(define extend-enforce-fns (extend-parameter enforce-fns))

(define fixpoint-enforce-fns (make-parameter '()))
(define extend-fixpoint-enforce-fns (extend-parameter fixpoint-enforce-fns))

;; runs all the enforce-constraint functions in enforce-fns
;; and all the fixpoint-enforce-fns in fixpoint-enforce-fns.. to a fixpoint
(define (enforce-constraints x)
  (fresh ()
    (let ([fns (fixpoint-enforce-fns)]
          [strat (search-strategy)])
      (fixpoint-enforce x (pick-strat strat) fns))
    (for/fold ([f unitg])
              ([fn (map cdr (enforce-fns))])
      (fresh () (fn x) f))))

;; default strategy is dfs, bfs also included
(define search-strategy (make-parameter 'dfs))

(define (pick-strat st)
  (case st
    [(dfs) cycle-dfs]
    [(bfs) cycle-bfs]
    [else (error 'pick-strat "unknown strategy ~s" st)]))

;; runs the given search strategy on the queue of lazy goals
(define (fixpoint-enforce x strat fns)
  (lambdag@ (a : s c q)
    (cond
     [(empty-q? q) a]
     [else ((strat x q fns) (make-a s c empty-q))])))

(define (cycle-dfs x q fns)
  (fresh ()
    (cond
     [(empty-q? q) succeed]
     [else
      (let-values ([(oc rest) (de-q q)])
        (fresh ()
          ((cdr (assq (oc-rator oc) fns)) x oc)
          (lambdag@ (a : s c q)
            (make-a s c (append-q rest q)))))])
    (fixpoint-enforce x cycle-dfs fns)))

(define (cycle-bfs x q fns)
  (fresh ()
    (let loop ([ocs (sort (fq:queue->list q) >ground-terms)])
      (cond
       [(null? ocs) succeed]
       [else 
        (let-values ([(oc rest) (values (car ocs) (cdr ocs))])
          (fresh ()
            ((cdr (assq (oc-rator oc) fns)) x oc)
            (loop rest)))]))
    (fixpoint-enforce x cycle-dfs fns)))

(define (ground-terms oc)
  (foldl + 0 (map (lambda (x) (if (var? x) 0 1)) (oc-rands oc))))

(define (>ground-terms oc1 oc2)
  (> (ground-terms oc1) (ground-terms oc2)))
  
(define-syntax (define-lazy-goal stx)
  (syntax-parse stx
    [(define-lazy-goal (name args ...) body)
     (with-syntax ([lazy-name (format-id #'name "lazy-~a" (syntax-e #'name))]
                   [enforce-name (format-id #'name "enforce-~a" (syntax-e #'name))])
       #'(begin
           (define (name args ...)
             (goal-construct (lazy-name args ...)))
           (define (lazy-name args ...)
             (lambdam@ (a : s c)
               ((update-c (build-lazy-goal-oc lazy-name (walk* args s) ...)) a)))
           (define (enforce-name x oc)
             (match (oc-rands oc)
               [`(,args ...) body]
               [_ (error "internal error, won't get here")]))
           (extend-fixpoint-enforce-fns 'lazy-name enforce-name)))]
    [(define-lazy-goal name (lambda (args ...) body))
     #'(define-lazy-goal (name args ...) body)]))

;; == REIFICATION ==============================================================

;; a list of functions to be run during reification
(define reify-fns        (make-parameter '()))
(define extend-reify-fns (extend-parameter reify-fns))

(define reify-with-colon (make-parameter #t))

;; reifies the constraint store with respect to x
(define (reify x)
  (lambdag@ (a : s c)
    (define v (walk* x s))
    (define-values (v^ r) (reify-s v empty-s))
    (define answer
      (cond
       ((null? r) v^)
       (else (reify-constraints (walk* v^ r) r c))))
    (choiceg answer empty-f)))

(define (reify-cvar cvar r) (walk cvar r))

;; reifies the substitution, returning the reified substitution
(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) 
       (let ([v^ (reify-n v (size-s s))])
         (values v^ `((,v . ,v^) . ,s))))
      ((mk-struct? v) 
       (recur v
        (lambda (a d)
          (define-values (a^ r) (reify-s a s))
          (define-values (d^ r^) (reify-s d r))
          (values (mk-struct->sexp
                   ((constructor v) a^ d^))
                  r^))))
      (else (values v s)))))

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

(define ((default-reify sym cs fn) v r ocs)
  (let ((ocs (filter-memq/rator cs ocs)))
    (let ((rands (filter-not any/var? (walk* (map oc-rands ocs) r))))
      (cond
       ((null? rands) `())
       (else `((,sym . ,(sort (fn rands) lex<=))))))))

(define (sort-store ocs) (sort ocs lex<= #:key car))

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

;; convenience macro to integrate Scheme and cKanren, 
;; returns n answers to the goals g0 g1 ... where x is fresh
(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g1 ...)
     (take n (lambdaf@ ()
               ((fresh (x) g0 g1 ...
                  (enforce-constraints x) 
                  (reify x))
                empty-a))))))

;; RUNS ALL THE THINGS
(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

;; == HELPERS ========================================================

(define (any/var? p)
  (cond
    ((pair? p)
     (or (any/var? (car p)) (any/var? (cdr p))))
    (else (var? p))))

(define (any-relevant/var? t x*)
  (cond
    ((pair? t)
     (or (any-relevant/var? (car t) x*)
         (any-relevant/var? (cdr t) x*)))
    (else (and (var? t) (memq t x*)))))

(define (prefix-s s s^)
  (define (loop s^) 
    (cond
     [(eq? s^ s) '()] 
     [else (cons (car s^) (loop (cdr s^)))]))
  (if (null? s) s^ (loop s^)))


