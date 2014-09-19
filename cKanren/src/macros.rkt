#lang racket

(require (for-syntax syntax/parse racket/syntax racket/match racket)
         "syntax-classes.rkt"
         "constraints.rkt"
         "events.rkt"
         syntax/parse racket/syntax
         "helpers.rkt"
         "mk-structs.rkt"
         "framework.rkt"
         "triggers.rkt"
         "operators.rkt")

(provide define-constraint-type
         transformer)

(provide define-constraint
         constraint
         add-constraint-event
         remove-constraint-event)

(provide define-constraint-interaction
         spawn-constraint-interactions)

(provide removed-constraint
         added-constraint)

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

(define-for-syntax (parse-responses stx bindings)
  (syntax-parse stx
    [((~literal =>) stuff ...)
     #`(lambda (ans) 
         ((let #,bindings stuff ...) 
          (car ans)))]
    [(stuff ...) 
     #`(lambda (ans) (let #,bindings stuff ...))]))

(define-syntax (define-constraint-interaction stx)
  (syntax-parse stx 
    [(define-constraint-interaction 
       rest ...
       [constraint-exprs ...] (~literal =>) [constraints ...])
     #'(define-constraint-interaction
         rest ...
         [constraint-exprs ...]
         [#t [constraints ...]])]
    [(define-constraint-interaction 
       (~or (~seq ci-name:id) (~seq))
       (constraint-exprs ...)
       (~or (~once pkgkw:package-keyword))
       ...
       clauses ...)
     (define/with-syntax name 
       (or (attribute ci-name) (generate-temporary #'?name)))
     (define/with-syntax (a [s c e]) #'pkgkw.package)
     (define/with-syntax initfn
       #`(create-interaction-fn
          name (constraint-exprs ...) (clauses ...)
          (a [s c e])))
     #'(extend-constraint-interactions
        initfn initfn)]))

(begin-for-syntax
 (define-splicing-syntax-class reaction-keyword
   #:attributes (name [args 1] [response 1])
   (pattern (~seq #:reaction [(name args ...) response ...]))
   (pattern (~seq #:reaction-to-event [(_name _args ...) _response ...])
            #:with (args ...) #'()
            #:with name 
            #'(trigger (match-lambda [(struct _name _) #t] [_ #f])
                       (lambda ()
                         (lambda@ (a [s c q t e]) 
                           (match-lambda ;; this is the e coming in
                             [(struct _name (_args ...)) (list _args ...)]
                             [_ #f]))))
            #:with (response ...)
            #'(=> (lambda (_args ...) _response ...))))
)

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
                          (~once reifykw:reification-keyword)
                          (~once uniquekw:unique-keyword))
                     ...)
               body:expr ...)
             (define/with-syntax (a [s c e]) #'pkgkw.package)
             (define/with-syntax bindings
               #'([args.arg (args.fn args.arg s c e)] ...))
             (define/with-syntax (response ...)
               (map (curryr parse-responses #'bindings)
                    (syntax->list #'((rkw.response ...) ...))))
             (define/with-syntax reify-body
               (syntax-parse #'reifykw.reified
                 [#t #'((default-reify 'fn-name args.arg ...) ans r)]
                 [#f #f]
                 [(#t expr) #'(reified-constraint 'fn-name expr r)]
                 [(#f expr) #'(expr ans r)]))
             (define/with-syntax reifyfn
               (cond
                [(syntax-e #'reifykw.reified) 
                 #'(lambda (args.arg ...)
                     (lambda (ans r)
                       (let ([args.arg (args.fn args.arg r)] ...)
                         reify-body)))]
                [else #'#f]))
             (define/with-syntax sub-to-associations?
               (cond
                [(null? (syntax-e #'(rkw.name ...)))
                 #'(association-event? e)]
                [else #'#f]))
             (define/with-syntax reaction-length
               (length (syntax-e #'(rkw.name ...))))
             (define/with-syntax (index ...)
               (range 0 (syntax-e #'reaction-length)))
             (define/with-syntax (interp ...) 
               (generate-temporaries #'(rkw.name ...)))
             (define/with-syntax (subs ...) 
               (generate-temporaries #'(rkw.name ...)))
             (define/with-syntax reaction
               ;; Event -> Response
               ;; A Response is a 
               ;;   Rands ... -> Package -> [List-of (cons Event ConstraintTransformer)]
               ;; at this point, we are given an event that we vaguely
               ;; care about
               #`(let ([subs   (trigger-subs rkw.name)] ...
                       [interp (trigger-interp rkw.name)] ...)
                   (lambda (e^) 
                     (define all-matching-events 
                       (filter (lambda (e) (or (subs e) ... sub-to-associations?)) e^))
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
                              [(((interp rkw.args ...) a) an-e)
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
                                       ;; todo: why is this walking in just an-e
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
                         (and (not (null? rets^)) rets^))))))
             (define/with-syntax unique-expr
               (syntax-parse #'uniquekw.unique
                 [#t #'((define-constraint-interaction 
                          [(fn-name args.arg ...) (fn-name args.arg ...)]
                          => [(fn-name args.arg ...)]))]
                 [#f #'()]))
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
                          ;; TODO WTF IS GOING ON DOWN THERE
                          (cond
                           [(cond
                             [(reaction e)
                              => (lambda (a-response)
                                   ((a-response args.arg ...) a))])
                            => (match-lambda
                                 [(list (cons an-e ct) (... ...))
                                  (bindm a (sum ct))])]
                           [(cond
                             [(reaction (empty-event))
                              => (lambda (a-response)
                                   ((a-response args.arg ...) a))])
                            => (match-lambda
                                 [(list (cons an-e ct) (... ...))
                                  (bindm a (sum ct))])]
                           [else (bindm a entire-body)])))
                      reaction reifyfn add rem))))
             #'(begin pattern . unique-expr)]))))]))

(define-syntax (transformer stx)
  (syntax-parse stx
    [(transformer 
      (~seq (~or (~once pkgkw:package-keyword))
            ...)
      body:expr ...)
     (define/with-syntax (a [s c e]) #'pkgkw.package)
     #'(lambda@ (a [s c q t e])
         (bindm a (let () body ...)))]))

(define-constraint-type constraint walk*)

(define constraint-interactions
  (make-parameter '()))

(define extend-constraint-interactions
  (extend-parameter constraint-interactions))

(define (spawn-constraint-interactions)
  (for/fold ([fn succeed]) ([ci (constraint-interactions)])
    (conj ((cdr ci)) fn)))

(define-trigger (removed-constraint ocs)
  [(remove-constraint-event/internal rator rands)
   (=> abort)
   (or (memq rands (map cdr ocs)) (abort))])

(define-trigger (added-constraint missing)
  [(add-constraint-event/internal rator rands)
   (=> abort)
   ;; this has to be cons (atm) because we have a list in the
   ;; constraint-interaction user interface with unquotes.
   ;; TODO: get rid of the unquotes.
   (let ([ans (missing (cons rator rands))])
     (or ans (abort)))])

(define-syntax (create-initial-missing stx)
  (syntax-parse stx
    ;; if we are out of patterns, we have found all the things we are looking for!
    ;; all of the ocs are in scope and we just have to match them against the patterns
    [(create-initial-missing 
      [[a s c e] name [pred? [constraints ...]] ...]
      (sat-ocs ... last-oc)
      (sat-patterns ...) 
      () ())
     (define/with-syntax rem-ocs 
       #'(conj (remove-constraint (oc (car sat-ocs) (cdr sat-ocs)))
               ...
               (remove-constraint (oc (car last-oc) (cdr last-oc)))))
     (define/with-syntax (sat-constraints ...)
       (map (lambda (cs) 
              (syntax-parse cs
                [((~literal add) cs ...) #'(conj cs ...)]
                [(cs ...) #'(conj rem-ocs cs ...)]))
            (syntax->list #'([constraints ...] ...))))
     ;; YOU NEED PERMUTATIONS BECAUSE: REFLEXICVIVITY.
     (define/with-syntax ((patterns ...) ...)
       (permutations (syntax-e #'(sat-patterns ...))))
     (define/with-syntax (temps ...)
       (generate-temporaries #'(sat-patterns ...)))
     #'(lambda@ (a [s c q t e])
         (match (list sat-ocs ... last-oc)
           [(list patterns ...)
            (=> abort)
            (cond
             [pred? (bindm a sat-constraints)]
             ...
             [else (abort)])]
           ...
           ;; if we really do satisfy the pattern, but we didn't
           ;; satisfy any of the pred?s in any order, then there's not
           ;; much we can do
           ;; TODO: WTF LIST-NO-ORDER
           [(list patterns ...) a]
           ...))]
    ;; if we are just out of post-patterns, that means we have already
    ;; made all the possible levels of matches and our new-oc just
    ;; doesn't work at all
    [(create-initial-missing 
      [stuff ...]
      (sat-ocs ...) (sat-patterns ...) (unsat-patterns ...) ())
     #'(lambda (new-oc) #f)]
    [(create-initial-missing 
      [[a s c e] name [pred? [constraints ...]] ...]
      ;; the names of ocs that have been satisfied
      (sat-ocs ...)
      ;; the patterns satisfied by those ocs
      (sat-patterns ...)
      ;; unsatisfied patterns
      (unsat-patterns-pre ...) (unsat-pattern unsat-patterns-post ...))
     ;; TODO: matching MORE THAN ONE.
     (define/with-syntax result
       #'(lambda (new-oc)
           (cond
            ;; if you IMMEDIATELY try to add a constraint that is ptr
            ;; equivalent to one you already have, give up
            [(memq (cdr new-oc) (map cdr (list sat-ocs ...))) #f]
            [else
             (match (list new-oc (list sat-ocs ...))
               [(list unsat-pattern (list sat-patterns ...))
                ;; we have figured out that new-oc satisfies one of our
                ;; unsatisfied patterns!  so, we have to return a
                ;; CONSTRAINT that processes it accordingly -- i.e. either
                ;; we have all the things we want, OR, we don't, and we
                ;; have to simply add a new constraint with a new missing?
                ;; to the store
                (let ([fn (create-initial-missing 
                           [[a s c e] name [pred? [constraints ...]] ...]
                           (sat-ocs ... new-oc)
                           (sat-patterns ... unsat-pattern)
                           () (unsat-patterns-pre ... unsat-patterns-post ...))])
                  (cond
                   [(transformer? fn) fn]
                   [(procedure? fn) (cons new-oc fn)]))]
               [_
                ((create-initial-missing
                  [[a s c e] name [pred? [constraints ...]] ...]
                  (sat-ocs ...) (sat-patterns ...)
                  (unsat-patterns-pre ... unsat-pattern) (unsat-patterns-post ...))
                 new-oc)])])))
     #'result]))

(require racket/trace)

;; forms a constraint-interaction-expr, which should be a function
;; that expects an oc and returns a constraint that, when it runs,
;; adds a lazy constraint to the store for every possible permutation
;; of the constraint-exprs
(define-syntax (create-interaction-fn stx)
  (syntax-parse stx
    [(create-interaction-fn
      name 
      ([rator rands ...] ...)
      ([pred? [constraints ...]] ...)
      (a [s c e]))
     ;; a function that decides whether or not a new even e is
     ;; relevant to the constraint-interaction; i.e, whether it
     ;; contains an oc that we are missing from ocs to make up
     ;; `((rands ...) ...)
     (define/with-syntax (unsat-patterns ...)
       #'((cons (? (curry eq? rator) _) (list rands ...))
          ...))  
     ;; expands to a FUNCTION that expects a new-oc and returns EITHER
     ;; #f, if the new-oc is irrelevant, OR a constraint that should be run!
     (define/with-syntax initial-missing
       #'(create-initial-missing 
          [[a s c e] name [pred? [constraints ...]] ...]
          () () ; sats
          ()    ; pre
          (unsat-patterns ...)))
     ;; this constraint will be run if a constraint is missing is
     ;; added, or if a constraint that we already count on is removed.
     #'(let ()
         (define-constraint (name [ocs #:constant] [missing #:constant])
          #:package (a [s c e])
          #:reaction
          [(removed-constraint ocs)
           succeed]
          #:reaction
          [(added-constraint missing)
           => 
           ;; will enter this function once for every new oc that is
           ;; within the original event e, and do a conj of that whole
           ;; thing
           (lambda (result)
             (define fn
               (cond
                [(transformer? result) 
                 result]
                [(pair? result)
                 (match-define (cons new-oc fn^) result)
                 (name (cons new-oc ocs) fn^)]
                [(false? result)
                 succeed]))
             (conj (add-constraint (name ocs missing)) fn))])
        (lambda () (name (list) initial-missing)))]))


