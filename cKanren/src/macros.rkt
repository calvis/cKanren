#lang racket

(require (for-syntax syntax/parse racket/syntax racket/match racket)
         "syntax-classes.rkt"
         "constraints.rkt"
         "events.rkt"
         syntax/parse racket/syntax
         "helpers.rkt"
         "mk-structs.rkt"
         "framework.rkt"
         "triggers.rkt")

(provide define-constraint-type
         transformer)

(provide define-constraint
         constraint
         add-constraint-event
         remove-constraint-event)

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
               (null? (syntax-e #'(rkw.name ...))))
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
                               (or ((trigger-subs rkw.name) e) ... 
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
