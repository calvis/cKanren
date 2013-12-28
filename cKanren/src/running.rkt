#lang racket

(require (for-syntax syntax/parse racket/syntax "framework.rkt" racket/pretty "syntax-classes.rkt")
         "framework.rkt" syntax/parse racket/syntax racket/pretty "helpers.rkt"
         "operators.rkt" "constraints.rkt" "events.rkt" "package.rkt" "syntax-classes.rkt"
         racket/generator "infs.rkt" "constraint-interactions.rkt" "variables.rkt")

(provide (all-defined-out))

(define-syntax (run/lazy stx)
  (syntax-parse stx
    [(run/lazy (x:id) g:expr ...)
     (define/with-syntax initialize-interactions
       #'(spawn-constraint-interactions
          (constraint-interactions)))
     (define/with-syntax prog 
       #'(let ([x (var 'x)])
           (conj g ... (enforce x) (reify x))))
     (define/with-syntax initial-a-inf
       #'(delay (bindm empty-a (conj initialize-interactions prog))))
     (syntax/loc #'stx
       (let ([a-inf initial-a-inf])
         (generator () (take/lazy a-inf))))]))

;; convenience macro to integrate Scheme and cKanren, 
;; returns n answers to the goals g0 g1 ... where x is fresh
(define-syntax (run stx)
  (syntax-parse stx
    [(_ n:expr (x:id) g0:expr g1:expr ...)
     (syntax/loc stx
       (let ([stream (run/lazy (x) g0 g1 ...)])
         (take n stream)))]
    [(_ n:expr (x:id ...) g:expr ...)
     (syntax/loc stx
       (run n (q) (fresh (x ...) (add-association q `(,x ...)) g ...)))]))

;; RUNS ALL THE THINGS
(define-syntax (run* stx)
  (syntax-parse stx
    [(_ (x ...) g ...) 
     (syntax/loc stx (run #f (x ...) g ...))]))

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
        'name initfn)]))

(define-syntax (case/lazy stx)
  (syntax-parse stx
    [(_ gen [() no-answer-clause:expr] [(x:id g:id) an-answer-clause:expr])
     (syntax/loc stx
       (let ([g gen])
         (call-with-values (lambda () (g))
           (case-lambda
            [() no-answer-clause]
            [(x) an-answer-clause]))))]))

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
     #'(running x (bindm empty-a (conj succeed g ...)))]))

(define-syntax-rule 
  (resume/interactive state g ...)
  (let ([st state])
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (running x (bindm a-inf (conj succeed g ...))))))

(define-syntax-rule 
  (enforce/interactive state)
  (let ([st state])
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (enforced x (bindm a-inf (enforce x))))))

(define-syntax-rule
  (reify/interactive state)
  (let ([st state])
    (unless (enforced? st)
      (error 'reify/interactive "trying to reify an unenforced state ~s" st))
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (bindm a-inf (reify x)))))

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

