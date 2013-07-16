#lang racket

(require "ck.rkt" "tree-unify.rkt")
(require (for-syntax racket racket/syntax syntax/parse))
;; (provide matche defmatche)
(provide (all-defined-out))

(define-syntax (defmatche stx)
  (syntax-parse stx
    [(defmatche (name:id args:id ...) clause ...)
     #'(define (name args ...)
         (matche (args ...) clause ...))]))

(define-syntax lambdae
  (syntax-rules ()
    ((_ (x ...) c c* ...)
     (lambda (x ...) (matche (x ...) (c c* ...))))))

(define-syntax (matche stx)
  (syntax-parse stx
    [(matche (v:id ...) (pat g ...) ...)
     (define args (syntax-e #'(v ...)))
     (define depth 1)
     (with-syntax*
      ([((pat (x ...) (c ...)) ...) 
        (map (lambda (pat) (wpat pat args depth))
             (syntax-e #'(pat ...)))]
       [((x ...) ...) (map (lambda (ls) 
                             (remove-duplicates (syntax-e ls) free-identifier=?))
                           (syntax-e #'((x ...) ...)))])
      #'(let ([ls (list v ...)])
          (conde [(fresh (x ...) (== `pat ls) c ... g ...)] ...)))]))

(define-for-syntax (guard-pattern-var-is-arg x args depth)
  (when (and (or (not depth) (not (zero? depth)))
             (ormap ((curry free-identifier=?) x) args))
    (error 'matche "argument ~s appears more than once at different depths" 
           (syntax-e x))))

(define-for-syntax (wpat pat args depth)
  (syntax-case pat (unquote _ ?)
    [(unquote _)
     (guard-pattern-var-is-arg #'x args depth)
     (with-syntax ([_new (generate-temporary #'?_)])
       #'((unquote _new) (_new) ()))]
    [(unquote (? c x))
     (guard-pattern-var-is-arg #'x args depth)
     #'((unquote x) (x) ((c x)))]
    [(unquote x)
     (guard-pattern-var-is-arg #'x args depth)
     #'((unquote x) (x) ())]
    [(a ...)
     (let ([depth (and depth (> depth 0) (sub1 depth))])
       (with-syntax
         ([((pat (x ...) (c ...)) ...)
           (map (lambda (a) (wpat a args depth)) (syntax-e #'(a ...)))])
         #'((pat ...) (x ... ...) (c ... ...))))]
    [(a . d)
     (let ([depth #f])
       (with-syntax
         ([((pat1 (x1 ...) (c1 ...)) (pat2 (x2 ...) (c2 ...)))
           (map (lambda (a) (wpat a args depth)) (syntax-e #'(a d)))])
         #'((pat1 . pat2) (x1 ... x2 ...) (c1 ... c2 ...))))]
    [x #'(x () ())]))



