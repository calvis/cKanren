#lang racket

(require racket/generic) 

(provide
 ;; framework for defining constraints
 update-s update-c make-a any/var? prefix-s prtm
 lambdam@ identitym composem goal-construct ext-c
 build-oc oc->proc oc->rands oc->rator run run* prt
 extend-enforce-fns extend-reify-fns goal? a? 
 walk walk* var? lambdag@ mzerog unitg onceo
 conde conda condu ifa ifu project fresh succeed fail
 lambdaf@ inc enforce-constraints reify empty-a take
 format-source
 (for-syntax build-srcloc))

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

;; write-var controls how variables are displayed
(define (write-var var port mode)
  ((parse-mode mode) (format "#~a(~s)" (cvar->str var) (var-x var)) port))

(define (parse-mode mode)
  (case mode [(#t) write] [(#f) display] [else display]))

;; == GOALS ====================================================================

;; a goal is just a function that can be applied to a's
(struct goal (fn) #:property prop:procedure (struct-field-index fn))

;; macro to return a goal with the specified function
(define-syntax lambdag@
  (syntax-rules (:)
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

(define-syntax-rule (fresh (x ...) g g* ...)
  (lambdag@ (a) 
    (inc 
     (let ((x (var 'x)) ...) 
       (bindg* (app-goal g a) g* ...)))))

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
         (bindg* (app-goal g1 a) g^ ...) ...))))))

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
      ((pair? v)
       (cons
        (walk* (car v) s)
        (walk* (cdr v) s)))
      (else v))))

;; a function that will safely extend the subsitution with
;; a binding of x to v
(define (update-s-check x v)
  (lambdam@ (a : s c)
    (let ((x (walk x s))
          (v (walk v s)))
      (cond
        ((or (var? x) (var? v))
         ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
          (make-a (ext-s x v s) c)))
        ((equal? x v) a)
        (else #f)))))

;; a function that will insecurely extend the substitution 
;; with a binding of x to v 
(define (update-s-nocheck x v)
  (lambdam@ (a : s c)
    ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
     (make-a (ext-s x v s) c))))

(define update-s update-s-check)

;; == CONSTRAINT STORE =========================================================

(struct constraint-store (c)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-constraint-store args))])

;; an empty constraint store
(define empty-c '())

;; extends the constraint store c with oc
(define (ext-c oc c) (cons oc c))

(define (write-constraint-store constraint-store port mode)
  ((parse-mode mode) (format "~a" (constraint-store-c constraint-store)) port))

;; adds oc to the constraint store if it contains a non-ground var
(define update-c
  (lambda (oc)
    (lambdam@ (a : s c)
      (cond
        ((any/var? (oc->rands oc))
         (make-a s (ext-c oc c)))
        (else a)))))

;; == PACKAGE ==================================================================

;; a package is a structure containing a substitution and
;; a constraint store
(struct a (s c) 
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-package args))])

(define (make-a s c) 
  (a (substitution s) (constraint-store c)))

;; the empty package
(define empty-a (make-a empty-s empty-c))

;; controls how packages are displayed
(define (write-package a port mode)
  ((parse-mode mode)
   (format "(~a . ~a)" (a-s a) (a-c a)) port))

;; == CONSTRAINTS ========================================================================

;; special lambda for defining constraints
(define-syntax lambdam@
  (syntax-rules (:)
    [(_ (a) e ...) 
     (lambda (a) e ...)]
    [(_ (a : s c) e ...)
     (lambdam@ (a) 
       (let ([s (substitution-s (a-s a))] 
             [c (constraint-store-c (a-c a))]) 
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
  #:methods gen:custom-write 
  [(define (write-proc . args) (apply write-oc args))])

(define make-oc oc)

(define (write-oc oc port mode)
  (define fn (lambda (str) ((parse-mode mode) str port)))
  (fn (format "(~a" (oc-rator oc)))
  (for ([arg (oc-rands oc)])
    (fn (format " ~a" arg)))
  (fn (format ")")))

;; accessors
(define oc->proc  oc-proc)
(define oc->rator oc-rator)
(define oc->rands oc-rands)

;; creates an oc given the constraint operation and it's args
(define-syntax (build-oc x)
  (syntax-case x ()
    ((_ op arg ...)
     (with-syntax ([(arg^ ...) (generate-temporaries #'(arg ...))])
       #'(let ((arg^ arg) ...)
           (make-oc (op arg^ ...) 'op `(,arg^ ...)))))))

;; == FIXPOINT =================================================================

;; fixed point algorithm given some variables x* that have changed,
;; and a constraint store c.  will rerun any constraints that 
;; mention x*
(define (run-constraints x* c)
  (for/fold ([rest identitym])
            ([oc c]
             #:when (any-relevant/var? (oc->rands oc) x*))
    (composem rest (rem/run oc))))

;; removes a constraint from the constraint store and then 
;; reruns it as if it was just being introduced (will add itself
;; back to the constraint store if it still is waiting on info)
(define (rem/run oc)
  (lambdam@ (a : s c)
    (cond
      ((memq oc c)
       ((oc->proc oc)
        (make-a s (remq oc c))))
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

;; runs all the enforce-constraint functions in enforce-fns
(define (enforce-constraints x)
  (for/fold ([f unitg])
            ([fn (map cdr (enforce-fns))])
    (fresh () (fn x) f)))

;; == REIFICATION ==============================================================

;; a list of functions to be run during reification
(define reify-fns   (make-parameter '()))
(define extend-reify-fns   (extend-parameter reify-fns))

;; reifies the constraint store with respect to x
(define (reify x)
  (lambdag@ (a : s c)
    (define v (walk* x s))
    (define r (reify-s v empty-s))
    (define answer
      (cond
       ((null? r) v)
       (else (reify-constraints (walk* v r) r c))))
    (choiceg answer empty-f)))

;; reifies the substitution, returning the reified substitution
(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) `((,v . ,(reify-n v (size-s s))) . ,s))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

;; creates a reified symbol
(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar->str cvar) (number->string n))))

;; reifies the constraint store by running all the reification fns
(define (reify-constraints v r c)
  (cond
    ((null? c) v)
    (else
     (let ((c^ (run-reify-fns v r c)))
       (if (null? c^) v `(,v : . ,c^))))))

;; runs all the reification functions
(define run-reify-fns
  (lambda (v r c)
    (for/fold ([c^ `()])
              ([fn (map cdr (reify-fns))])
       (append (fn v r c) c^))))

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


