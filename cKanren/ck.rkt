#lang racket

(require racket/generic 
         racket/stxparam
         racket/generator
         "src/helpers.rkt"
         "src/errors.rkt"
         "src/operators.rkt"
         "src/infs.rkt"
         "src/structs.rkt")

(require (for-syntax 
          syntax/parse
          racket/syntax
          "src/errors.rkt"))

(provide
 var? define-var-type goal? make-a c->list empty-s empty-c
 update-s update-c any/var?  prefix-s prtm identitym composem
 goal-construct ext-c build-oc oc-rands oc-rator run run* prt
 extend-enforce-fns extend-reify-fns goal? a?  walk walk*
 mzerog unitg onceo fresh-aux conde conda condu ifa ifu project fresh
 succeed fail enforce reify empty-a take mzerom bindm constraint?
 format-source reify-cvar var ext-s gen:mk-struct recur constructor
 mk-struct?  lex<= sort-by-lex<= reify-with-colon default-mk-struct?
 occurs-check run-relevant-constraints build-attr-oc attr-oc?  attr-oc-uw?
 get-attributes filter/rator filter-not/rator default-reify attr-oc-type
 filter-memq/rator define-lazy-goal replace-ocs same-default-type?
 override-occurs-check? update-c-nocheck reify-term var-x ext-c*
 filter-not-memq/rator #%app-safe use-constraints debug replace-s
 update-s-nocheck update-s-prefix attr-tag update-package lambdam@
 default-reify-attr define-constraint-interaction run-constraints
 run/lazy case/lazy start/interactive resume/interactive reify/interactive 
 lambdag@
 enforce/interactive exit/interactive extend-subscriptions conj)

(provide (rename-out [trace-define-mk trace-define]))

(provide 
 (for-syntax search-strategy))

(define attr-tag 'attr)

;; == PARAMETERS ===============================================================

(define ((extend-parameter param) tag fn)
  (let ((fns (param)))
    (and (not (assq tag fns))
         (param (cons `(,tag . ,fn) fns)))))

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
  (lambdam@/private (a : s c q t)
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
  (lambdag@/private (a : s c q t)
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
  (lambdag@/private (a : s c q t)
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
     (let ([a-inf ((fresh (x) g ... (enforce x) (reify x)) empty-a)])
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
       name
       (constraint-exprs ...)
       (~or (~optional (~seq #:package (a:id : s:id c:id)))
            (~optional (~seq (~and #:not-reflexive reflexive?))))
       ...
       clauses ...)
     (define a-name (or (attribute a) (generate-temporaries #'(?a))))
     (define s-name (or (attribute s) (generate-temporaries #'(?s))))
     (define c-name (or (attribute c) (generate-temporaries #'(?c))))
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
       ([(arg ...) (generate-temporaries #'(rator ...))]
        [bad-pattern-error 
         #'(error 'name "bad pattern ~s" '((rator rands ...) ...))])
       #`(let ()
           (define (run-interaction . arg*)
             (lambdam@/private (a : ?s ?c ?q ?t)
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
                   [_ bad-pattern-error]))))
           (define (name oc)
             (let ([this-rator (oc-rator oc)])
               (lambdam@ (a : s c)
                 (generate-cond run-interaction (a s c) oc this-rator 
                                () ((rator rands ...) ...)))))
           name))]))

(define-syntax (generate-cond stx)
  (syntax-parse stx 
    [(generate-cond run-interaction (a s c) oc this-rator (pattern ...) ()) #'#f]
    [(generate-cond 
      run-interaction (a s c) oc this-rator
      ((rator-pre rand-pre) ...)
      ((rator rand ...) (rator-post rand-post) ...))
     (with-syntax
      ([(pre ...) (generate-temporaries #'(rator-pre ...))]
       [(post ...) (generate-temporaries #'(rand-post ...))])
      (with-syntax*
       ([(pre-ocs ...)  #'((filter/rator 'rator-pre c) ...)]
        [(post-ocs ...) #'((filter/rator 'rator-post c) ...)]
        [pattern-applies? #'(eq? 'rator this-rator)]
        [run-rule
         #'(bindm a
             (for*/fold
              ([fn mzerom])
              ([pre    pre-ocs] ...
               [this (list oc)]
               [post  post-ocs] ...)
              (lambdam@ (a : s c)
                (cond
                 [((run-interaction pre ... this post ...) a)]
                 [else (fn a)]))))]
        [rest-formatted 
         #'(generate-cond 
            run-interaction (a s c) oc this-rator
            ((rator-pre rand-pre) ... (rator rand ...))
            ((rator-post rand-post) ...))])
       #'(or (and pattern-applies? run-rule) rest-formatted)))]))

