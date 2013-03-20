#lang racket

(require racket/generic) 

(provide
 ;; framework for defining constraints
 update-s update-c make-a any/var? prefix-s prtm
 lambdam@ identitym composem goal-construct ext-c
 build-oc oc->proc oc->rands oc->rator run run* prt
 extend-enforce-fns extend-reify-fns goal? a? 
 lhs rhs walk walk* var? lambdag@ mzerog unitg onceo
 conde conda condu ifa ifu project fresh succeed fail
 lambdaf@ inc enforce-constraints reify empty-a take
 safe-goals?)

(define safe-goals? (make-parameter #f))

(define-generics constrained-var)

(define (write-var var port mode)
  ((case mode [(#t) write] [(#f) display] [else print])
   (format "#(~s)" (var-x var)) port))

;; vars are actually constrained-vars  
(define-struct var (x) 
  #:transparent 
  #:methods gen:constrained-var ()
  #:methods gen:custom-write ([define write-proc write-var]))

(define lhs (lambda (x) (car x)))
(define rhs (lambda (x) (cdr x)))

;; a goal is just a function that can be applied to a's
(define-struct goal (fn)
  #:property prop:procedure (struct-field-index fn))

;; macro to return a goal with the specified function
(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (a : s c) e ...)
     (lambdag@ (a) (let ((s (a-s a)) (c (a-c a))) e ...)))
    ((_ (a) e ...) (make-goal (lambda (a) e ...)))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define (walk v s)
  (cond
    ((var? v)
     (let ((a (assq v s)))
       (cond
         (a (walk (rhs a) s))
         (else v))))
    (else v)))

(define (walk* w s)
  (let ((v (walk w s)))
    (cond
      ((var? v) v)
      ((pair? v)
       (cons
        (walk* (car v) s)
        (walk* (cdr v) s)))
      (else v))))

;; the failure value
(define (mzerog) #f)

;; the identity goal
(define unitg (lambdag@ (a) a))

;; succeed and fail are the simplest succeeding and failing goals
(define succeed unitg)
(define fail    (lambdag@ (a) (mzerog)))

;; for debugging, a goal that prints the substitution and a goal
;; that prints a message.  both succeed.
(define prt  (lambdag@ (a) (begin (pretty-print a) a)))
(define prtm (lambda m (lambdag@ (a) (begin (apply printf m) a))))

(define-syntax inc 
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

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

;; hard to explain
(define empty-f (lambdaf@ () (mzerog)))
(define choiceg cons)

;; given a number n and an infinite stream f, takes answers from f
(define (take n f)
  (cond
    ((and n (zero? n)) '())
    (else
     (case-inf (f)
       (() '())
       ((f) (take n f))
       ((a) (cons a '()))
       ((a f) (cons a (take (and n (- n 1)) f)))))))

(define-syntax wrap-goal
  (syntax-rules ()
    [(_ g)
     (if (safe-goals?) 
         (let ((g^ g)) (safe-goal-wrap 'g g^)) 
         g)]))

(define (safe-goal-wrap orig val)
  (cond
   [(goal? val) val] 
   [else (error 'ck "~s evaluated to ~s which is not a goal" orig val)]))

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
      ((a) ((wrap-goal g) a))
      ((a f) (mplusg ((wrap-goal g) a) (lambdaf@ () (bindg (f) g)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a) 
       (inc 
        (mplusg* 
         (bindg* ((wrap-goal g0) a) g ...)
         (bindg* ((wrap-goal g1) a) g^ ...) ...))))))

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

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc (ifa (((wrap-goal g0) a) g ...) 
                 (((wrap-goal g1) a) g^ ...) ...))))))

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

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc
        (ifu (((wrap-goal g0) a) g ...)
             (((wrap-goal g1) a) g^ ...) ...))))))

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

(define-syntax-rule (fresh (x ...) g g* ...)
  (lambdag@ (a) 
    (inc 
     (let ((x (var 'x)) ...) 
       (bindg* ((wrap-goal g) a) g* ...)))))

(define-syntax project 
  (syntax-rules ()
    ((_ (x ...) g g* ...)  
     (lambdag@ (a : s c)
       (let ((x (walk* x s)) ...)
         ((fresh () g g* ...) a))))))

(define onceo (lambda (g) (condu (g))))

;; ---SUBSITUTION--------------------------------------------------

;; the empty substitution
(define empty-s '())

;; extends a substitution with a binding of x to v
(define (ext-s x v s) (cons `(,x . ,v) s))

;; returns the size of a substitution
(define size-s
  (lambda (x)
    (length x)))

;; a function that will safely extend the subsitution with
;; a binding of x to v
(define (update-s-check x v)
  (lambdam@ (a : s c)
    (let ((x (walk x s))
          (v (walk v s)))
      (cond
        ((or (var? x) (var v))
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

(define update-s update-s-nocheck)

;; ---CONSTRAINT-STORE---------------------------------------------

;; an empty constraint store
(define empty-c '())

;; extends the constraint store c with oc
(define (ext-c oc c) (cons oc c))

;; adds oc to the constraint store if it contains a non-ground var
(define update-c
  (lambda (oc)
    (lambdam@ (a : s c)
      (cond
        ((any/var? (oc->rands oc))
         (make-a s (ext-c oc c)))
        (else a)))))

;; ---PACKAGE------------------------------------------------------

;; a package is a structure containing a substitution and
;; a constraint store
(define-struct a (s c) #:transparent)

;; the empty package
(define empty-a (make-a empty-s empty-c))

;; ---M-PROCS------------------------------------------------------

;; special lambda for defining constraints
(define-syntax lambdam@
  (syntax-rules (:)
    ((_ (a) e ...) 
     (lambda (a) e ...))
    ((_ (a : s c) e ...)
     (lambdam@ (a) (let ((s (a-s a)) (c (a-c a))) e ...)))))

;; the identity constraint
(define identitym (lambdam@ (a) a))

;; composes two constraints together
(define (composem fm f^m)
  (lambdam@ (a)
    (let ((a (fm a)))
      (and a (f^m a)))))

;; constructs a goal from a constraint
(define (goal-construct fm) (lambdag@ (a) (fm a)))

;; ---BUILD-OC-----------------------------------------------------

;; the representation of a constraint in the constraint store 
;; contains a closure waiting to be evaluated with a new package,
;; a symbolic representation of the constrant's name and it's args
(define-struct oc (proc rator rands) #:transparent)

;; accessors
(define oc->proc oc-proc)
(define oc->rator oc-rator)
(define oc->rands oc-rands)

;; creates an oc given the constraint operation and it's args
(define-syntax build-oc
  (syntax-rules ()
    ((_ op arg ...)
     (build-oc-aux op (arg ...) () (arg ...)))))

(define-syntax build-oc-aux
  (syntax-rules ()
    ((_ op () (z ...) (arg ...))
     (let ((z arg) ...) 
       (make-oc (op z ...) 'op `(,z ...))))
    ((_ op (arg0 arg ...) (z ...) args)
     (build-oc-aux op (arg ...) (z ... q) args))))

;; ---FIXED-POINT--------------------------------------------------

;; fixed point algorithm given some variables x* that have changed,
;; and a constraint store c.  will rerun any constraints that 
;; mention x*
(define (run-constraints x* c)
  (cond
    ((null? c) identitym)
    ((any-relevant/var? (oc->rands (car c)) x*)
     (composem
      (rem/run (car c))
      (run-constraints x* (cdr c))))
    (else (run-constraints x* (cdr c)))))

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

;; ---PARAMETERS---------------------------------------------------

;; a list of functions to be run during enforce-constraints
;; and reification
(define enforce-fns (make-parameter '()))
(define reify-fns (make-parameter '()))

;; extends the parameters
(define ((extend-parameter param) tag fn)
  (let ((fns (param)))
    (and (not (assq tag fns))
         (param (cons `(,tag . ,fn) fns)))))

(define extend-enforce-fns (extend-parameter enforce-fns))
(define extend-reify-fns (extend-parameter reify-fns))

;; ---ENFORCE-CONSTRAINTS------------------------------------------

;; runs all the enforce-constraint functions in enforce-fns
(define (enforce-constraints x)
  (let loop ((fns (enforce-fns)))
    (cond
      ((null? fns) unitg)
      (else (fresh () ((cdar fns) x) (loop (cdr fns)))))))

;; ---REIFICATION--------------------------------------------------

;; reifies the constraint store with respect to x
(define (reify x)
  (lambdag@ (a : s c)
    (let* ((v (walk* x s))
           (r (reify-s v empty-s)))
      (choiceg
       (cond
         ((null? r) v)
         (else (reify-constraints (walk* v r) r c)))
       empty-f))))

;; reifies the substitution
(define (reify-s v s)
  (let ((v (walk v s)))
    (cond
      ((var? v) `((,v . ,(reify-n (size-s s))) . ,s))
      ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
      (else s))))

;; creates a reified symbol
(define (reify-n n)
  (string->symbol
   (string-append "_" "." (number->string n))))

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
    (let loop ((fns (reify-fns)) (c^ `()))
      (cond
        ((null? fns) c^)
        (else (loop (cdr fns) (append ((cdar fns) v r c) c^)))))))

;; ---MACROS-------------------------------------------------------

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

;; RUN ALL THE THINGS
(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

;; ---HELPERS------------------------------------------------------

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

(define prefix-s
  (lambda (s s^)
    (cond
      ((null? s) s^)
      (else
       (let loop ((s^ s^))
         (cond
           ((eq? s^ s) '())
           (else (cons (car s^) (loop (cdr s^))))))))))

;; ----------------------------------------------------------------

