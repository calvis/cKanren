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
     (lambda (x ...) (matche (x ...) c c* ...)))))

(define-syntax (matche stx)
  (syntax-parse stx
    [(matche (v:id ...) ([pat ...] g ...) ...)
     (define/with-syntax (([pat^ ...] (x ...)) ...)
       (map (curry parse-pattern (syntax-e #'(v ...)))
            (syntax-e #'([pat ...] ...))))
     (define/with-syntax ((x^ ...) ...) 
       (map (compose (lambda (ls) 
                       (remove-duplicates ls free-identifier=?))
                     syntax-e)
            (syntax-e #'((x ...) ...))))
     (define/with-syntax body 
       #'(conde
          [(fresh (x^ ...) (== `[pat^ ...] ls) g ...)]
          ...))
     #'(let ([ls (list v ...)]) body)]
    [(matche v:id (pat g ...) ...)
     #'(matche (v) ([pat] g ...) ...)]))

(define-for-syntax (parse-pattern args pat)
  (syntax-parse #`(#,args #,pat)
    [(() ()) #'(() ())]
    [((a args ...) [p pat ...])
     (define/with-syntax (p^ (x ...))
       (parse-patterns-for-arg #'a #'p))
     (define/with-syntax ([pat^ ...] (x^ ...))
       (parse-pattern #'(args ...) #'[pat ...]))
     #'([p^ pat^ ...] (x ... x^ ...))]))

(define-for-syntax (parse-patterns-for-arg v pat)
  (define (loop pat)
    (syntax-parse pat
      [((~literal unquote) (~literal _))
       (define/with-syntax _new (generate-temporary #'?_))
       #'((unquote _new) (_new))]
      [((~literal unquote) x:id)
       (when (free-identifier=? #'x v)
         (error 'matche "argument ~s appears in pattern at an invalid depth" 
                (syntax-e #'x)))
       #'((unquote x) (x))]
      [(a ...)
       (define/with-syntax ((pat (x ...)) ...)
         (map loop (syntax-e #'(a ...))))
       #'((pat ...) (x ... ...))]
      [(a . d)
       (define/with-syntax ((pat1 (x1 ...)) (pat2 (x2 ...)))
         (map loop (syntax-e #'(a d))))
       #'((pat1 . pat2) (x1 ... x2 ...))]
      [x #'(x ())]))
  (cond
   [(and (identifier? pat)
         (free-identifier=? v pat))
    #'(v ())]
   [else (loop pat)]))

(module+ test
  (defmatche (foo a b)
    [[5 5]])

  (run* (x y) (foo x y)))



