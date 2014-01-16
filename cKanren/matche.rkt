#lang racket

(require cKanren/ck cKanren/tree-unify cKanren/tester)
(require (for-syntax racket racket/syntax syntax/parse))

(provide defmatche lambdae matche)

(define-syntax (defmatche stx)
  (syntax-parse stx
    [(defmatche (name:id args:id ...) clause ...)
     (syntax/loc stx
       (define (name args ...)
         (matche (args ...) clause ...)))]))

(define-syntax lambdae
  (syntax-rules ()
    ((_ (x ...) c c* ...)
     (lambda (x ...) (matche (x ...) c c* ...)))))

(define-syntax (matche stx)
  (syntax-parse stx
    [(matche (v:id ...) ([pat ...] g ...) ...)
     (define v-length (length (syntax-e #'(v ...))))
     (for ([a-pat (syntax->list (syntax/loc stx ([pat ...] ...)))])
       (unless (= (length (syntax->list a-pat)) v-length)
         (raise-syntax-error 
          'matche
          (format "expected pattern of length ~a" v-length)
          a-pat)))
     (define/with-syntax (([pat^ ...] (c ...) (x ...)) ...)
       (map (curry parse-pattern #'(v ...))
            (syntax-e #'([pat ...] ...))))
     (define/with-syntax ((x^ ...) ...) 
       (map (compose (curryr remove-duplicates free-identifier=?) syntax-e)
            (syntax-e #'((x ...) ...))))
     (define/with-syntax body
       #'(conde
          [(fresh (x^ ...) c ... (== `[pat^ ...] ls) g ...)]
          ...))
     (syntax/loc stx (let ([ls (list v ...)]) body))]
    [(matche v:id (pat g ...) ...)
     (syntax/loc stx (matche (v) ([pat] g ...) ...))]))

(define-for-syntax (parse-pattern args pat)
  (syntax-parse #`(#,args #,pat)
    [(() ()) #'(() () ())]
    [((a args ...) [p pat ...])
     (define/with-syntax (p^ (c ...) (x ...))
       (parse-patterns-for-arg #'a #'p))
     (define/with-syntax ([pat^ ...] (c^ ...) (x^ ...))
       (parse-pattern #'(args ...) #'[pat ...]))
     #'([p^ pat^ ...] (c ... c^ ...) (x ... x^ ...))]
    [x (error 'parse-pattern "bad syntax ~s ~s" args pat)]))

(define-for-syntax (parse-patterns-for-arg v pat)
  (define (loop pat)
    (syntax-parse pat
      [((~literal unquote) (~literal _))
       (define/with-syntax _new (generate-temporary #'?_))
       #'((unquote _new) () (_new))]
      [((~literal unquote) x:id)
       (when (free-identifier=? #'x v)
         (error 'matche "argument ~s appears in pattern at an invalid depth" 
                (syntax-e #'x)))
       #'((unquote x) () (x))]
      [((~literal unquote) ((~literal ?) c:expr))
       (define/with-syntax _new (generate-temporary #'?_))
       #'((unquote _new) ((c _new)) (_new))]
      [((~literal unquote) ((~literal ?) c:expr x:id))
       (when (free-identifier=? #'x v)
         (error 'matche "argument ~s appears in pattern at an invalid depth" 
                (syntax-e #'x)))
       #'((unquote x) ((c x)) (x))]
      [(a . d)
       (define/with-syntax 
         ((pat1 (c1 ...) (x1 ...)) 
          (pat2 (c2 ...) (x2 ...)))
         (map loop (syntax-e #'(a d))))
       #'((pat1 . pat2) (c1 ... c2 ...) (x1 ... x2 ...))]
      [x #'(x () ())]))
  (syntax-parse pat
    [((~literal unquote) u:id)
     (cond
      [(and (identifier? #'u)
            (free-identifier=? v #'u))
       #'((unquote u) () ())]
      [else (loop pat)])]
    [((~literal unquote) ((~literal ?) c:id u:id))
     (cond
      [(and (identifier? #'u)
            (free-identifier=? v #'u))
       #'((unquote u) ((c x)) ())]
      [else (loop pat)])]
    [else (loop pat)]))

(module+ test

  (let ()
    (defmatche (foo a b)
      [[5 5]])
    (test
     (run* (q) (foo 5 5))
     '(_.0))
    (test
     (run* (q) (foo q 5))
     '(5))
    (test
     (run* (x y) (foo x y))
     '((5 5))))
    
  (let ()
    (defmatche (bar a)
      [[(,x . ,y)]
       (== x y)])
    (test
     (run* (q) (bar q))
     '((_.0 . _.0))))

  (let () 
    (defmatche (baby-rembero x ls out)
      [[,x () ()]])
    (test
     (run* (q) (baby-rembero 'x '() '()))
     '(_.0))))



