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
     (unless 
       (andmap (compose (curry = (length (syntax-e #'(v ...))))
                        length syntax-e)
               (syntax-e #'([pat ...] ...)))
       (error 'matche "pattern wrong length blah"))
     (define/with-syntax (([pat^ ...] (x ...)) ...)
       (map (curry parse-pattern #'(v ...))
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
     #'([p^ pat^ ...] (x ... x^ ...))]
    [x (error 'parse-pattern "bad syntax ~s ~s" args pat)]))

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
      [(a . d)
       (define/with-syntax ((pat1 (x1 ...)) (pat2 (x2 ...)))
         (map loop (syntax-e #'(a d))))
       #'((pat1 . pat2) (x1 ... x2 ...))]
      [x #'(x ())]))
  (syntax-parse pat
    [((~literal unquote) u:id)
     (cond
      [(and (identifier? #'u)
            (free-identifier=? v #'u))
       #'((unquote u) ())]
      [else (loop pat)])]
    [else (loop pat)]))

(module+ test
  (require (prefix-in ru: rackunit))

  (let ()
    (defmatche (foo a b)
      [[5 5]])
    (ru:check-equal?
     (run* (q) (foo 5 5))
     '(_.0))
    (ru:check-equal?
     (run* (q) (foo q 5))
     '(5))
    (ru:check-equal?
     (run* (x y) (foo x y))
     '((5 5))))
    
  (let ()
    (defmatche (bar a)
      [[(,x . ,y)]
       (== x y)])
    (ru:check-equal?
     (run* (q) (bar q))
     '((_.0 . _.0))))

  (let () 
    (defmatche (baby-rembero x ls out)
      [[,x () ()]])
    (ru:check-equal?
     (run* (q) (baby-rembero 'x '() '()))
     '(_.0))))



