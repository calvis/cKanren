#lang racket

(require 
 "../ck.rkt"
 "../absento.rkt"
 "../tree-unify.rkt"
 "../neq.rkt"
 "../tester.rkt"
 (for-syntax "../ck.rkt"))

(provide test-quines test-quines-long)

(begin-for-syntax
 (define strat 'dfs)
 (search-strategy strat))

(define-lazy-goal (eval-expo exp env val)
;; (define (eval-expo exp env val)
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
   ((symbolo exp) (lookupo exp env val))
   ((fresh (rator rand x body env^ a)
      (== `(,rator ,rand) exp)
      (eval-expo rator env `(closure ,x ,body ,env^))
      (eval-expo rand env a)
      (eval-expo body `((,x . ,a) . ,env^) val)))
   ((fresh (x body)
      (== `(lambda (,x) ,body) exp)
      (symbolo x)
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

(define-lazy-goal proper-listo
;; (define proper-listo
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
  (parameterize ([reify-with-colon #f]
                 [reify-prefix-dot #f])
    
    (test "1 quine"
          (time (run 1 (q) (eval-expo q '() q)))
          '((((lambda (_.0) (list _.0 (list 'quote _.0)))
              '(lambda (_.0) (list _.0 (list 'quote _.0))))
             (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
             (sym _.0))))
    
    (test "2 quines"
          (time (run 2 (q) (eval-expo q '() q)))
          '((((lambda (_.0) (list _.0 (list (quote quote) _.0))) 
              (quote (lambda (_.0) (list _.0 (list (quote quote) _.0)))))
             (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) 
             (sym _.0)) 
            (((lambda (_.0) 
                (list (list (quote lambda) (quote (_.0)) _.0)
                      (list (quote quote) _.0))) 
              (quote (list (list (quote lambda) (quote (_.0)) _.0) 
                           (list (quote quote) _.0)))) 
             (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) 
             (sym _.0))))

    (test-check "3 quines"
                (run 3 (q) (eval-expo q '() q))
                '((((lambda (_.0) (list _.0 (list (quote quote) _.0)))
                    (quote (lambda (_.0) (list _.0 (list (quote quote) _.0))))) 
                   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) 
                  (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0)))
                    (quote (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))
                   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) 
                  (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2))))
                    (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2))))))
                   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) 
                        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) 
                   (absento (closure _.2)) (sym _.0 _.1))))
)

)

(define (test-quines-long)
  (test-quines)

  (parameterize ([reify-with-colon #f]
                 [reify-prefix-dot #f])
    (test-check "5 quines"
                (run 5 (q) (eval-expo q '() q))
                '((((lambda (_.0) (list _.0 (list (quote quote) _.0))) (quote (lambda (_.0) (list _.0 (list (quote quote) _.0))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))) (quote (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0)))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))) (list (quote quote) _.0))) (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1))))

    (test-check "10 quines"
                (run 10 (q) (eval-expo q '() q))
                '((((lambda (_.0) (list _.0 (list (quote quote) _.0))) (quote (lambda (_.0) (list _.0 (list (quote quote) _.0))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))) (quote (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0)))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))) (list (quote quote) _.0))) (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list _.1 _.0)) (quote quote)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list _.1 _.0)) (quote quote)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list))) (sym _.0 _.1)) (((lambda (_.0) ((lambda (_.1) (list _.0 (list (quote quote) _.0))) (quote _.2))) (quote (lambda (_.0) ((lambda (_.1) (list _.0 (list (quote quote) _.0))) (quote _.2))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) _.1) (quote quote)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) _.1) (quote quote)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (sym _.0 _.1)) (((lambda (_.0) (list ((lambda (_.1) _.0) (quote _.2)) (list (quote quote) _.0))) (quote (lambda (_.0) (list ((lambda (_.1) _.0) (quote _.2)) (list (quote quote) _.0))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) (quote _.4)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) (quote _.4)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2))))

    (test-check "40 quines"
                (run 40 (q) (eval-expo q '() q))
                '((((lambda (_.0) (list _.0 (list (quote quote) _.0))) (quote (lambda (_.0) (list _.0 (list (quote quote) _.0))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))) (quote (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0)))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) (quote _.2)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))) (list (quote quote) _.0))) (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (quote (list (quote quote) _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list _.1 _.0)) (quote quote)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list _.1 _.0)) (quote quote)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list))) (sym _.0 _.1)) (((lambda (_.0) ((lambda (_.1) (list _.0 (list (quote quote) _.0))) (quote _.2))) (quote (lambda (_.0) ((lambda (_.1) (list _.0 (list (quote quote) _.0))) (quote _.2))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) _.1) (quote quote)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) _.1) (quote quote)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (sym _.0 _.1)) (((lambda (_.0) (list ((lambda (_.1) _.0) (quote _.2)) (list (quote quote) _.0))) (quote (lambda (_.0) (list ((lambda (_.1) _.0) (quote _.2)) (list (quote quote) _.0))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) (quote _.4)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) (quote _.4)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list _.2 _.0)) (quote quote))) (quote _.3)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list _.2 _.0)) (quote quote))) (quote _.3)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) ((lambda (_.1) (list _.0 (list _.1 _.0))) (quote quote))) (quote (lambda (_.0) ((lambda (_.1) (list _.0 (list _.1 _.0))) (quote quote))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list))) (sym _.0 _.1)) (((lambda (_.0) ((lambda (_.1) (list (list (quote lambda) (quote (_.0)) (list _.1 (list (quote quote) _.1))) (quote (quote _.2)))) (quote (lambda (_.1) (list (list (quote lambda) (quote (_.0)) (list _.1 (list (quote quote) _.1))) (quote (quote _.2))))))) (quote _.2)) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (list (quote quote) (list (quote quote) _.0)))) (quote (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (list (quote quote) (list (quote quote) _.0)))))))) (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (list (quote quote) (list (quote quote) _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) ((lambda (_.1) (list _.1 (list (quote quote) _.1))) _.0)) (quote (lambda (_.0) ((lambda (_.1) (list _.1 (list (quote quote) _.1))) _.0)))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (sym _.0 _.1)) (((lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.0 (list (quote quote) _.0))) (quote _.3))) (quote _.4))) (quote (lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.0 (list (quote quote) _.0))) (quote _.3))) (quote _.4))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list _.1 _.0)) (quote _.3))) (quote quote)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list _.1 _.0)) (quote _.3))) (quote quote)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 _.2)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list ((lambda (_.2) (quote quote)) (quote _.3)) _.0)) (quote _.4)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list ((lambda (_.2) (quote quote)) (quote _.3)) _.0)) (quote _.4)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) ((lambda (_.1) (list (list (quote lambda) (quote (_.0)) (list _.1 (list _.0 _.1))) (quote (quote quote)))) (quote (lambda (_.1) (list (list (quote lambda) (quote (_.0)) (list _.1 (list _.0 _.1))) (quote (quote quote))))))) (quote quote)) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.1)) _.0))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.1)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) ((lambda (_.3) (list _.3 _.0)) (quote quote))) (quote _.4))) (quote _.5)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) ((lambda (_.3) (list _.3 _.0)) (quote quote))) (quote _.4))) (quote _.5)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 lambda)) ((_.2 list)) ((_.2 quote)) ((_.3 closure)) ((_.3 list))) (absento (closure _.4) (closure _.5)) (sym _.0 _.1 _.2 _.3)) (((lambda (_.0) ((lambda (_.1) (list _.1 (list (quote quote) _.0))) _.0)) (quote (lambda (_.0) ((lambda (_.1) (list _.1 (list (quote quote) _.0))) _.0)))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (sym _.0 _.1)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) ((lambda (_.2) (quote quote)) (quote _.3))) (quote _.4)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) ((lambda (_.2) (quote quote)) (quote _.3))) (quote _.4)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 quote)) ((_.2 closure)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 (list (quote quote) ((lambda (_.1) _.0) (quote _.2))))) (quote (lambda (_.0) (list _.0 (list (quote quote) ((lambda (_.1) _.0) (quote _.2))))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) _.0))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) _.0)) _.0))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote))) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list ((lambda (_.2) _.2) (quote quote)) _.0)) (quote _.3)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list ((lambda (_.2) _.2) (quote quote)) _.0)) (quote _.3)))))) (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (list (quote list) (quote (quote quote)) (quote _.0)))) (list (quote quote) _.0))) (quote (list (quote lambda) (quote (_.0)) (list (quote list) _.0 (list (quote list) (quote (quote quote)) (quote _.0)))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((lambda (_.0) (list _.0 (list (quote quote) ((lambda (_.1) ((lambda (_.2) _.0) (quote _.3))) (quote _.4))))) (quote (lambda (_.0) (list _.0 (list (quote quote) ((lambda (_.1) ((lambda (_.2) _.0) (quote _.3))) (quote _.4))))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 quote)) ((_.2 closure))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) ((lambda (_.2) _.0) (quote _.3)))) (quote _.4)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) (list (quote quote) ((lambda (_.2) _.0) (quote _.3)))) (quote _.4)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 (list ((lambda (_.1) ((lambda (_.2) _.2) (quote quote))) (quote _.3)) _.0))) (quote (lambda (_.0) (list _.0 (list ((lambda (_.1) ((lambda (_.2) _.2) (quote quote))) (quote _.3)) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 quote)) ((_.2 closure))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list ((lambda (_.1) _.1) _.0) (list (quote quote) _.0))) (quote (lambda (_.0) (list ((lambda (_.1) _.1) _.0) (list (quote quote) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (sym _.0 _.1)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0))) (quote (list (list (quote lambda) (quote (_.0)) _.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) _.0)))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) _.1)) (quote _.3)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) _.1)) (quote _.3)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) ((lambda (_.3) (list (quote quote) _.0)) (quote _.4))) (quote _.5))) (quote _.6)))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) ((lambda (_.3) (list (quote quote) _.0)) (quote _.4))) (quote _.5))) (quote _.6)))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 lambda)) ((_.2 list)) ((_.2 quote)) ((_.3 closure)) ((_.3 list)) ((_.3 quote))) (absento (closure _.4) (closure _.5) (closure _.6)) (sym _.0 _.1 _.2 _.3)) (((lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.0 (list _.2 _.0))) (quote quote))) (quote _.3))) (quote (lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.0 (list _.2 _.0))) (quote quote))) (quote _.3))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.1)) (quote _.3))) _.0))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.1)) (quote _.3))) _.0))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 _.2)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list (list (quote lambda) (quote (_.0)) (list _.1 (list (quote quote) _.1))) (quote (quote _.3)))) (quote _.4))) (quote (lambda (_.1) ((lambda (_.2) (list (list (quote lambda) (quote (_.0)) (list _.1 (list (quote quote) _.1))) (quote (quote _.3)))) (quote _.4)))))) (quote _.3)) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 _.2)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3) (closure _.4)) (sym _.0 _.1 _.2)) (((lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.1 (list (quote quote) _.1))) (quote _.3))) _.0)) (quote (lambda (_.0) ((lambda (_.1) ((lambda (_.2) (list _.1 (list (quote quote) _.1))) (quote _.3))) _.0)))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 _.2)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3)) (sym _.0 _.1 _.2)) (((lambda (_.0) (list (list (quote lambda) (quote (_.0)) _.0) (list ((lambda (_.1) _.1) (quote quote)) _.0))) (quote (list (list (quote lambda) (quote (_.0)) _.0) (list ((lambda (_.1) _.1) (quote quote)) _.0)))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure))) (sym _.0 _.1)) (((lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) _.0))) (quote (lambda (_.0) (list _.0 ((lambda (_.1) ((lambda (_.2) (list (quote quote) _.0)) (quote _.3))) _.0))))) (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda)) ((_.1 list)) ((_.1 quote)) ((_.2 closure)) ((_.2 list)) ((_.2 quote))) (absento (closure _.3)) (sym _.0 _.1 _.2))))

    (test-check "2 twines"
                (run 2 (x) (fresh (p q)
                             (=/= p q)
                             (eval-expo p '() q)
                             (eval-expo q '() p)
                             (== `(,p ,q) x)))
                '((((quote ((lambda (_.0) (list (quote quote) (list _.0 (list (quote quote) _.0)))) (quote (lambda (_.0) (list (quote quote) (list _.0 (list (quote quote) _.0))))))) ((lambda (_.0) (list (quote quote) (list _.0 (list (quote quote) _.0)))) (quote (lambda (_.0) (list (quote quote) (list _.0 (list (quote quote) _.0))))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((quote (list (quote quote) ((lambda (_.0) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0)))) (quote (lambda (_.0) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0)))))))) (list (quote quote) ((lambda (_.0) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0)))) (quote (lambda (_.0) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0)))))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0))))

    (test-check "4 thrines"
                (run 4 (x)
                  (fresh (p q r)
                    (=/= p q)
                    (=/= q r)
                    (=/= r p)
                    (eval-expo p '() q)
                    (eval-expo q '() r)
                    (eval-expo r '() p)
                    (== `(,p ,q ,r) x)))
                '((((quote (quote ((lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0))))))))) (quote ((lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0)))))))) ((lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote quote) (list _.0 (list (quote quote) _.0)))))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((quote (quote (list (quote quote) ((lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0)))))))))) (quote (list (quote quote) ((lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0))))))))) (list (quote quote) ((lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list (quote quote) (list (quote list) (quote (quote quote)) (list _.0 (list (quote quote) _.0))))))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0)) (((quote (quote ((lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0))))))))) (quote ((lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0)))))))) ((lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0))))) (quote (lambda (_.0) (list ((lambda (_.1) (quote quote)) (quote _.2)) (list (quote quote) (list _.0 (list (quote quote) _.0)))))))) (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 quote))) (absento (closure _.2)) (sym _.0 _.1)) (((quote (quote ((lambda (_.0) (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))) (quote (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0)))))))) (quote ((lambda (_.0) (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))) (quote (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))))) ((lambda (_.0) (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))) (quote (list (quote quote) (list (quote quote) (list (list (quote lambda) (quote (_.0)) _.0) (list (quote quote) _.0))))))) (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote))) (sym _.0))))))

(module+ main
  (test-quines-long))
