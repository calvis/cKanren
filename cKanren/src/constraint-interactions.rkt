#lang racket 

(require (for-syntax syntax/parse racket/syntax "framework.rkt"
                     (only-in racket/list permutations))
         "framework.rkt" syntax/parse racket/syntax "helpers.rkt"
         "operators.rkt" "constraints.rkt" "events.rkt" "package.rkt")

(provide (all-defined-out))

(define constraint-interactions
  (make-parameter '()))

(define extend-constraint-interactions
  (extend-parameter constraint-interactions))

(define (spawn-constraint-interactions cis)
  (for/fold ([fn succeed]) ([ci cis])
    (conj ((cdr ci)) fn)))

(define-trigger (removed-constraint ocs)
  [(remove-constraint-event/internal rator rands)
   (=> abort)
   (cond
    [(member rands (map cdr ocs))
     ;; (printf "found a removed: ~a\n" rands)
     #t]
    [else (abort)])])

(define-trigger (added-constraint missing)
  [(add-constraint-event/internal rator rands)
   (=> abort)
   ;; this has to be cons (atm) because we have a list in the
   ;; constraint-interaction user interface with unquotes.
   ;; TODO: get rid of the unquotes.
   (let ([ans (missing (cons rator rands))])
     (cond
      [ans
       ;; (printf "found a missing: ~a\n" ans)
       ans]
      [else (abort)]))])

(define-syntax (create-initial-missing stx)
  (syntax-parse stx
    ;; if we are out of patterns, we have found all the things we are looking for!
    ;; all of the ocs are in scope and we just have to match them against the patterns
    [(create-initial-missing 
      [[a s c e] name [pred? constraints ...] ...]
      (sat-ocs ... last-oc)
      (sat-patterns ...) 
      () ())
     (define/with-syntax rem-ocs 
       #'(conj (remove-constraint (oc (car sat-ocs) (cdr sat-ocs)))
               ...
               (remove-constraint (oc (car last-oc) (cdr last-oc)))))
     (define/with-syntax (sat-constraints ...)
       #'((conj rem-ocs constraints ...) ...))
     ;; YOU NEED PERMUTATIONS BECAUSE: REFLEXICVIVITY.
     (define/with-syntax ((patterns ...) ...)
       (permutations (syntax-e #'(sat-patterns ...))))
     (define/with-syntax (temps ...)
       (generate-temporaries #'(sat-patterns ...)))
     #'(lambda@ (a [s c q t e])
         ;; (printf "GOT THE RIGHT NUMBER OF THINGIES\n")
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
           ...
           ;; if we don't even satisfy the list-no-order, then wtf are we doing
           [_ (error 'name "internal error ~a\n" (list sat-ocs ... last-oc))]))]
    ;; if we are just out of post-patterns, that means we have already
    ;; made all the possible levels of matches and our new-oc just
    ;; doesn't work at all
    [(create-initial-missing 
      [stuff ...]
      (sat-ocs ...) (sat-patterns ...) (unsat-patterns ...) ())
     #'(lambda (new-oc) #f)]
    [(create-initial-missing 
      [[a s c e] name [pred? constraints ...] ...]
      ;; the names of ocs that have been satisfied
      (sat-ocs ...)
      ;; the patterns satisfied by those ocs
      (sat-patterns ...)
      ;; unsatisfied patterns
      (unsat-patterns-pre ...) (unsat-pattern unsat-patterns-post ...))
     ;; TODO: matching MORE THAN ONE.
     (define/with-syntax result
       #'(lambda (new-oc)
           ;; (printf "~a: checking ~s\n" 'name new-oc)
           (cond
            ;; if you IMMEDIATELY try to add a constraint that is ptr
            ;; equivalent to one you already have, give up
            [(memq (cdr new-oc) (map cdr (list sat-ocs ...))) #f]
            ; (error 'name "internal error memq: ~a ~a\n" new-oc (list sat-ocs ...))
            [else
             (match (list new-oc (list sat-ocs ...))
               [(list unsat-pattern (list sat-patterns ...))
                ;; we have figured out that new-oc satisfies one of our
                ;; unsatisfied patterns!  so, we have to return a
                ;; CONSTRAINT that processes it accordingly -- i.e. either
                ;; we have all the things we want, OR, we don't, and we
                ;; have to simply add a new constraint with a new missing?
                ;; to the store
                ;; (printf "FOUND A MATCH\n")
                (let ([fn (create-initial-missing 
                           [[a s c e] name [pred? constraints ...] ...]
                           (sat-ocs ... new-oc)
                           (sat-patterns ... unsat-pattern)
                           () (unsat-patterns-pre ... unsat-patterns-post ...))])
                  (cond
                   [(transformer? fn) fn]
                   [(procedure? fn) (cons new-oc fn)]
                   [else (error 'wut "wututtututt")]))]
               [_
                ;; (printf "didn't find a match\n")
                ((create-initial-missing
                  [[a s c e] name [pred? constraints ...] ...]
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
      ([pred? (constraints ...)] ...)
      (a [s c e]))
     (define/with-syntax (missing new-oc ocs)
       (generate-temporaries #'(missing new-oc ocs)))
     ;; a function that decides whether or not a new even e is
     ;; relevant to the constraint-interaction; i.e, whether it
     ;; contains an oc that we are missing from ocs to make up
     ;; `((rands ...) ...)
     (define/with-syntax (unsat-patterns ...)
       #'((cons (? (curry eq? rator) _) (list `rands ...))
          ...))  
     ;; expands to a FUNCTION that expects a new-oc and returns EITHER
     ;; #f, if the new-oc is irrelevant, OR a constraint that should be run!
     (define/with-syntax initial-missing
       #'(create-initial-missing 
          [[a s c e] name [pred? constraints ...] ...]
          () () ; sats
          ()    ; pre
          (unsat-patterns ...)))
     ;; this constraint will be run if a constraint is missing is
     ;; added, or if a constraint that we already count on is removed.
     #'(let ()
         (define-constraint (name ocs missing)
          #:package (a [s c e])
          #:reaction
          [(removed-constraint ocs)
           ;; (printf "removed needed constraint\n")
           succeed]
          #:reaction
          [(added-constraint missing)
           => 
           ;; will enter this function once for every new oc that is
           ;; within the original event e, and do a conj of that whole
           ;; thing
           (lambda (result)
             ;; (printf "found missing: ~a\n" result)
             (define fn
               (cond
                [(transformer? result) 
                 result]
                [(pair? result)
                 (match-define (cons new-oc fn^) result)
                 (name (cons new-oc ocs) fn^)]
                [(false? result)
                 succeed]
                [else (error 'name "here")]))
             (conj (add-constraint (name ocs missing)) fn))])
        (lambda () (name (list) initial-missing)))]))


