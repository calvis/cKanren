#lang racket

(require
 "../ck.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../absento.rkt"
 "../attributes.rkt"
 "../tester.rkt")
(provide test-interp test-interp-long)

(define (test-interp)
  (define not-in-envo
    (lambda (x env)
      (conde
       ((== '() env))
       ((fresh (y v rest)
          (== `((,y . ,v) . ,rest) env)
          (=/= y x)
          (not-in-envo x rest))))))

  (define lookupo-old
    (lambda (x env t)
      (conde
       ((fresh (y v rest)
          (== `((,y . ,v) . ,rest) env) (== y x)
          (== v t)))
       ((fresh (y v rest)
          (== `((,y . ,v) . ,rest) env) (=/= y x)
          (lookupo-old x rest t))))))
  
  (define eval-expo-old
    (lambda (exp env val)
      (conde
       ((fresh (rator rand x body env^ a)
          (== `(,rator ,rand) exp)
          (eval-expo-old rator env `(closure ,x ,body ,env^))
          (eval-expo-old rand env a)
          (eval-expo-old body `((,x . ,a) . ,env^) val)))
       ((fresh (x body)
          (== `(lambda (,x) ,body) exp)
          (symbol x)
          (== `(closure ,x ,body ,env) val)
          (not-in-envo 'lambda env)))
       ((symbol exp) 
        (lookupo-old exp env val)))))
  
  (test-check "running backwards"
              (run 5 (q) (eval-expo-old q '() '(closure y x ((x . (closure z z ()))))))
              '(((lambda (x) (lambda (y) x)) (lambda (z) z))
                (((lambda (x) ((lambda (_.0) _.0) (lambda (y) x))) (lambda (z) z)) (sym _.0))
                (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))
                (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0))
                ((lambda (x) (x (lambda (y) x))) (lambda (z) z))))
  
  (define eval-expo
    (lambda (exp env val)
      (conde
       ((fresh (rator rand x body env^ a)
          (== `(,rator ,rand) exp)
          (eval-expo rator env `(closure ,x ,body ,env^))
          (eval-expo rand env a)
          (eval-expo body `((,x . ,a) . ,env^) val)))
       ((fresh (x body)
          (== `(lambda (,x) ,body) exp)
          (symbol x)
          (== `(closure ,x ,body ,env) val)
          (not-in-envo 'lambda env)))
       ((symbol exp) (lookupo exp env val)))))

  (define lookupo
    (lambda (x env t)
      (fresh (rest y v)
        (== `((,y . ,v) . ,rest) env)
        (conde
         ((== y x) (== v t))
         ((=/= y x) (lookupo x rest t))))))

  (test-check "eval-exp-lc 1"
              (run* (q) (eval-expo '(((lambda (x) (lambda (y) x)) 
                                      (lambda (z) z)) (lambda (a) a)) '() q))
              '((closure z z ())))
  
  (test-check "eval-exp-lc 2"
              (run* (q) (eval-expo '((lambda (x) (lambda (y) x)) (lambda (z) z)) '() q))
              '((closure y x ((x . (closure z z ()))))))
  
  (test-check "running backwards"
              (run 5 (q) (eval-expo q '() '(closure y x ((x . (closure z z ()))))))
              '(((lambda (x) (lambda (y) x)) (lambda (z) z))
                ((lambda (x) (x (lambda (y) x))) (lambda (z) z))
                (((lambda (x) (lambda (y) x)) ((lambda (_.0) _.0) (lambda (z) z))) (sym _.0))
                (((lambda (_.0) _.0) ((lambda (x) (lambda (y) x)) (lambda (z) z))) (sym _.0))
                ((((lambda (_.0) _.0) (lambda (x) (lambda (y) x))) (lambda (z) z)) (sym _.0))))
  
  (test-check "fully-running-backwards"
              (run 5 (q)
                (fresh (e v)
                  (eval-expo e '() v)
                  (== `(,e ==> ,v) q)))
              '((((lambda (_.0) _.1)
                  ==> (closure _.0 _.1 ())) (sym _.0))
                ((((lambda (_.0) _.0) (lambda (_.1) _.2))
                  ==>
                  (closure _.1 _.2 ()))
                 (sym _.0 _.1))
                ((((lambda (_.0) (lambda (_.1) _.2)) (lambda (_.3) _.4))
                  ==>
                  (closure _.1 _.2 ((_.0 . (closure _.3 _.4 ())))))
                 (=/= ((_.0 lambda)))
                 (sym _.0 _.1 _.3))
                ((((lambda (_.0) (_.0 _.0)) (lambda (_.1) _.1))
                  ==>
                  (closure _.1 _.1 ()))
                 (sym _.0 _.1))
                ((((lambda (_.0) (_.0 _.0))
                   (lambda (_.1) (lambda (_.2) _.3)))
                  ==>
                  (closure _.2 _.3 ((_.1 . (closure _.1 (lambda (_.2) _.3) ())))))
                 (=/= ((_.1 lambda)))
                 (sym _.0 _.1 _.2))))
  )

(define (test-interp-long)
  (test-interp))

(module+ main
  (test-interp))
