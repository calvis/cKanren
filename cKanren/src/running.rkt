#lang racket

(require (for-syntax syntax/parse 
                     racket/syntax
                     "framework.rkt"
                     "syntax-classes.rkt")
         "framework.rkt" 
         syntax/parse
         racket/syntax
         racket/pretty
         "helpers.rkt"
         "operators.rkt" 
         "constraints.rkt"
         "events.rkt"
         "package.rkt"
         "syntax-classes.rkt"
         racket/generator 
         "infs.rkt"
         "macros.rkt"
         "variables.rkt")

(provide (all-defined-out))

(define-syntax (run/internal stx)
  (syntax-parse stx
    [(run/internal n:expr g:expr ...+)
     (define/with-syntax initialize-interactions
       #'(spawn-constraint-interactions))
     (define/with-syntax prog #'(conj g ...))
     (define/with-syntax initial-a-inf
       #'(delay (bindm empty-a (conj initialize-interactions prog))))
     (syntax/loc #'stx
       (take n (generator () (take/lazy initial-a-inf))))]))

(define-syntax (run/lazy stx)
  (syntax-parse stx
    [(run/lazy () g:expr ...)
     (define/with-syntax initialize-interactions
       #'(spawn-constraint-interactions))
     (define/with-syntax prog 
       #'(let ([x (var 'x)])
           (conj g ... (enforce x) (reifyc))))
     (define/with-syntax initial-a-inf
       #'(delay (bindm empty-a (conj initialize-interactions prog))))
     (syntax/loc #'stx
       (let ([a-inf initial-a-inf])
         (generator () (take/lazy a-inf))))]
    [(run/lazy (x:id) g:expr ...)
     (define/with-syntax initialize-interactions
       #'(spawn-constraint-interactions))
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
    [(_ n:expr () g0:expr g1:expr ...)
     (syntax/loc stx
       (let ([stream (run/lazy () g0 g1 ...)])
         (take n stream)))]
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
           ((parse-mode mode) "#<running/ir>" port))])

(struct enforced running ()
        #:methods gen:custom-write 
        [(define (write-proc ra port mode) 
           ((parse-mode mode) "#<running/ir>" port))])

(define-syntax (start/ir stx)
  (syntax-parse stx
    [(_ g ...) 
     (define/with-syntax initialize-interactions
       #'(spawn-constraint-interactions))
     (define/with-syntax initial-a-inf
       #'(delay (bindm empty-a (conj initialize-interactions prog))))
     #'(let ([x (var 'x)])
         (running x (delay (bindm empty-a (conj initialize-interactions g ...)))))]))

(define-syntax (extend/ir stx)
  (syntax-parse stx
    [(extend/ir state 
                (~optional (~seq #:var x)
                           #:defaults ([x (generate-temporary #'?x)]))
                g ...)
     #'(let ([st state])
         (let ([x (running-x st)]
               [a-inf (running-a-inf st)])
           (running x (bindm a-inf (conj succeed g ...)))))]))

(define-syntax-rule 
  (enforce/ir state)
  (let ([st state])
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (enforced x (bindm a-inf (enforce x))))))

(define-syntax-rule
  (reify/ir state)
  (let ([st state])
    (unless (enforced? st)
      (error 'reify/ir "trying to reify an unenforced state ~s" st))
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (bindm a-inf (reify x)))))

(define-syntax-rule
  (reifyc/ir state)
  (let ([st state])
    (unless (enforced? st)
      (error 'reify/ir "trying to reify an unenforced state ~s" st))
    (let ([x (running-x st)]
          [a-inf (running-a-inf st)])
      (bindm a-inf (reifyc)))))

(define-syntax (exit/ir stx)
  (syntax-parse stx
    [(exit/ir st) 
     #'(exit/ir #f st)]
    [(exit/ir n state)
     #'(let ([stream
              (generator 
               ()
               (take/lazy
                (let ([st state])
                  (reify/ir
                   (cond
                    [(enforced? st) st]
                    [else (enforce/ir st)])))))])
         (take n stream))]))

(define-syntax-rule (exit*/ir state) (exit/ir #f state))

(define-syntax (exitc/ir stx)
  (syntax-parse stx
    [(exitc/ir st)
     #'(exitc/ir #f st)]
    [(exitc/ir n state)
     #'(let ([stream
              (generator 
               ()
               (take/lazy
                (let ([st state])
                  (reifyc/ir
                   (cond
                    [(enforced? st) st]
                    [else (enforce/ir st)])))))])
         (take n stream))]))

