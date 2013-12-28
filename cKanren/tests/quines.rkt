#lang racket

(require 
 "../ck.rkt"
 "../absento.rkt"
 "../attributes.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../tester.rkt"
 (for-syntax "../ck.rkt"))

(provide test-quines test-quines-long)

;; (begin-for-syntax
;;  (define strat 'dfs)
;;  (search-strategy strat))

;; (define-lazy-goal (eval-expo exp env val)
(define (eval-expo exp env val)
  (conde
   ((fresh (v)
      (== `(quote ,v) exp)
      (not-in-envo 'quote env)
      (absento 'closure v)
      (== v val)))
   ((fresh (a*)
      (== `(list . ,a*) exp)
      (not-in-envo 'list env)
      (absento 'closure a*)
      (proper-listo a* env val)))
   ((symbol exp) (lookupo exp env val))
   ((fresh (rator rand x body env^ a)
      (== `(,rator ,rand) exp)
      (eval-expo rator env `(closure ,x ,body ,env^))
      (eval-expo rand env a)
      (eval-expo body `((,x . ,a) . ,env^) val)))
   ((fresh (x body)
      (== `(lambda (,x) ,body) exp)
      (symbol x)
      (not-in-envo 'lambda env)
      (== `(closure ,x ,body ,env) val)))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest)))
      ((== '() env)))))

;; (define-lazy-goal proper-listo
(define proper-listo
  (lambda (exp env val)
    (conde
     ((== '() exp)
      (== '() val))
     ((fresh (a d t-a t-d)
        (== `(,t-a . ,t-d) val)
        (== `(,a . ,d) exp)
        (eval-expo a env t-a)
        (proper-listo d env t-d))))))

(define lookupo
  (lambda (x env t)
    (fresh (rest y v)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

(define (test-quines)
  (test "1 quine"
        (time (run 1 (q) (eval-expo q '() q)))
        '((((lambda (_.0) (list _.0 (list 'quote _.0)))
            '(lambda (_.0) (list _.0 (list 'quote _.0))))
           (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
           (sym _.0))))
  
  (test "2 quines"
        (time (length (run 2 (q) (eval-expo q '() q))))
        2)

  (test "3 quines"
        (time (length (run 3 (q) (eval-expo q '() q))))
        3))

(define (test-quines-long)
  (test-quines)

  (test-check "5 quines"
              (time (length (run 5 (q) (eval-expo q '() q))))
              5)

  (test-check "10 quines"
              (time (length (run 10 (q) (eval-expo q '() q))))
              10)

  (test-check "40 quines"
              (time (length (run 40 (q) (eval-expo q '() q))))
              40)

  (test-check "2 twines"
              (time (length (run 2 (x) (fresh (p q)
                                         (=/= p q)
                                         (eval-expo p '() q)
                                         (eval-expo q '() p)
                                         (== `(,p ,q) x)))))
              2)

  (test-check "4 thrines"
              (time (length (run 4 (x)
                              (fresh (p q r)
                                (=/= p q)
                                (=/= q r)
                                (=/= r p)
                                (eval-expo p '() q)
                                (eval-expo q '() r)
                                (eval-expo r '() p)
                                (== `(,p ,q ,r) x)))))
              4))

(module+ main
  (test-quines-long))
