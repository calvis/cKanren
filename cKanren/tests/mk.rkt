#lang racket

(require
 "../miniKanren.rkt"
 "../absento.rkt"
 "../attributes.rkt"
 "../neq.rkt" 
 "../tester.rkt")
(provide test-mk test-mk-long)

  (define number-primo
    (lambda (exp env val)
      (fresh (n)
        (== `(intexp ,n) exp)
        (== `(intval ,n) val)
        (not-in-envo 'numo env))))

  (define sub1-primo
    (lambda (exp env val)
      (fresh (e n n-1)
        (== `(sub1 ,e) exp)
        (== `(intval ,n-1) val)
        (not-in-envo 'sub1 env)
        (eval-expo e env `(intval ,n))
        (minuso n '(1) n-1))))

  (define zero?-primo
    (lambda (exp env val)
      (fresh (e n)
        (== `(zero? ,e) exp)
        (conde
         ((zeroo n) (== #t val))
         ((poso n) (== #f val)))
        (not-in-envo 'zero? env)
        (eval-expo e env `(intval ,n)))))

  (define *-primo
    (lambda (exp env val)
      (fresh (e1 e2 n1 n2 n3)
        (== `(* ,e1 ,e2) exp)
        (== `(intval ,n3) val)
        (not-in-envo '* env)
        (eval-expo e1 env `(intval ,n1))
        (eval-expo e2 env `(intval ,n2))
        (*o n1 n2 n3))))

  (define if-primo
    (lambda (exp env val)
      (fresh (e1 e2 e3 t)
        (== `(if ,e1 ,e2 ,e3) exp)
        (not-in-envo 'if env)
        (eval-expo e1 env t)
        (conde
         ((== #t t) (eval-expo e2 env val))
         ((== #f t) (eval-expo e3 env val))))))

  (define boolean-primo
    (lambda (exp env val)
      (conde
       ((== #t exp) (== #t val))
       ((== #f exp) (== #f val)))))

  (define eval-expo
    (lambda (exp env val)
      (conde
       ((boolean-primo exp env val))
       ((number-primo exp env val))
       ((sub1-primo exp env val))
       ((zero?-primo exp env val))
       ((*-primo exp env val))
       ((if-primo exp env val))
       ((symbol exp) (lookupo exp env val))
       ((fresh (rator rand x body env^ a)
          (== `(,rator ,rand) exp)
          (eval-expo rator env `(closure ,x ,body ,env^))
          (eval-expo rand env a)
          (eval-expo body `((,x . ,a) . ,env^) val)))
       ((fresh (x body)
          (== `(lambda (,x) ,body) exp)
          (symbol x)
          (== `(closure ,x ,body ,env) val)
          (not-in-envo 'lambda env))))))

  (define not-in-envo
    (lambda (x env)
      (conde
       ((fresh (y v rest)
          (== `((,y . ,v) . ,rest) env)
          (=/= y x)
          (not-in-envo x rest)))
       ((== '() env)))))

  (define lookupo
    (lambda (x env t)
      (fresh (rest y v)
        (== `((,y . ,v) . ,rest) env)
        (conde
         ((== y x) (== v t))
         ((=/= y x) (lookupo x rest t))))))


(define (test-mk)
  (test-check "0"
              (run* (q) succeed)
              '(_.0))

  (test-check "1"
              (run 1 (q) (== 5 q))
              '(5))

  (test-check "2"
              (run* (q)
                (conde
                 [(== 5 q)]
                 [(== 6 q)]))
              '(5 6))

  (test-check "3"
              (run* (q)
                (fresh (a d)
                  (conde
                   [(== 5 a)]
                   [(== 6 d)])
                  (== `(,a . ,d) q)))
              '((5 . _.0) (_.0 . 6)))

  (test-check "4"
              (run* (q) (appendo '(a b c) '(d e) q))
              '((a b c d e)))

  (test-check "5"
              (run* (q) (appendo q '(d e) '(a b c d e)))
              '((a b c)))

  (test-check "6"
              (run* (q) (appendo '(a b c) q '(a b c d e)))
              '((d e)))

  (test-check "7"
              (run 5 (q)
                (fresh (l s out)    
                  (appendo l s out)
                  (== `(,l ,s ,out) q)))
              '((() _.0 _.0)
                ((_.0) _.1 (_.0 . _.1))
                ((_.0 _.1) _.2 (_.0 _.1 . _.2))
                ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
                ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))))

  (test-check "test 1"
              (run* (q) (*o (build-num 2) (build-num 3) q))
              '((0 1 1)))
  
  (test-check "test 2"
              (run* (q)
                (fresh (n m)    
                  (*o n m (build-num 6))
                  (== `(,n ,m) q)))
              '(((1) (0 1 1)) ((0 1 1) (1)) ((0 1) (1 1)) ((1 1) (0 1))))

  (test-check "push-down problems 2"
              (run* (q)
                (fresh (x a d)
                  (absento 'intval x)
                  (== 'intval a)
                  (== `(,a . ,d) x)))
              '())

  (test-check "push-down problems 3"
              (run* (q)
                (fresh (x a d)
                  (== `(,a . ,d) x)
                  (absento 'intval x)
                  (== 'intval a)))
              '())

  (test-check "push-down problems 4"
              (run* (q)
                (fresh (x a d)
                  (== `(,a . ,d) x)
                  (== 'intval a)
                  (absento 'intval x)))
              '())

  (test-check "push-down problems 6"
              (run* (q)
                (fresh (x a d)
                  (== 'intval a)
                  (== `(,a . ,d) x)
                  (absento 'intval x)))
              '())

  (test-check "push-down problems 1"
              (run* (q)
                (fresh (x a d)
                  (absento 'intval x)
                  (== `(,a . ,d) x)
                  (== 'intval a)))
              '())

  (test-check "push-down problems 5"
              (run* (q)
                (fresh (x a d)
                  (== 'intval a)
                  (absento 'intval x)
                  (== `(,a . ,d) x)))
              '())

  (test-check "zero?"
              (run 1 (q)
                (eval-expo `(zero? (sub1 (intexp ,(build-num 1)))) '() q))
              '(#t))

  (test-check "*"
              (run 1 (q)
                (eval-expo `(* (intexp ,(build-num 3)) (intexp ,(build-num 2))) 
                           '() 
                           `(intval ,(build-num 6))))
              '(_.0))

  (test-check "sub1"
              (run 1 (q)
                (eval-expo q '() `(intval ,(build-num 6))) (== `(sub1 (intexp ,(build-num 7))) q))
              '((sub1 (intexp (1 1 1)))))

  (test-check "sub1 bigger WAIT a minute"
              (run 1 (q)
                (eval-expo q '() `(intval ,(build-num 6)))
                (== `(sub1 (sub1 (intexp ,(build-num 8)))) q))
              '((sub1 (sub1 (intexp (0 0 0 1))))))

  (test-check "sub1 biggest WAIT a minute"
              (run 1 (q)
                (eval-expo q '() `(intval ,(build-num 6)))
                (== `(sub1 (sub1 (sub1 (intexp ,(build-num 9))))) q))
              '((sub1 (sub1 (sub1 (intexp (1 0 0 1)))))))

  (test-check "lots of programs to make a 6"
              (run 12 (q) (eval-expo q '() `(intval ,(build-num 6))))
              '((intexp (0 1 1))
                (sub1 (intexp (1 1 1)))
                (* (intexp (1)) (intexp (0 1 1)))
                (* (intexp (0 1 1)) (intexp (1)))
                (if #t (intexp (0 1 1)) _.0)
                (* (intexp (0 1)) (intexp (1 1)))
                (if #f _.0 (intexp (0 1 1)))
                (sub1 (* (intexp (1)) (intexp (1 1 1))))
                (sub1 (* (intexp (1 1 1)) (intexp (1))))
                (* (intexp (1 1)) (intexp (0 1)))
                (sub1 (if #t (intexp (1 1 1)) _.0))
                (((lambda (_.0) (intexp (0 1 1))) #t) (=/= ((_.0 numo))) (sym _.0)))
              #;
              '((intexp (0 1 1))
                (sub1 (intexp (1 1 1)))
                (* (intexp (1)) (intexp (0 1 1)))
                (* (intexp (0 1 1)) (intexp (1)))
                (* (intexp (0 1)) (intexp (1 1)))
                (if #t (intexp (0 1 1)) _.0)
                (sub1 (sub1 (intexp (0 0 0 1))))
                (* (intexp (1 1)) (intexp (0 1)))
                (sub1 (* (intexp (1)) (intexp (1 1 1))))
                (if #f _.0 (intexp (0 1 1)))
                (sub1 (* (intexp (1 1 1)) (intexp (1))))
                (((lambda (_.0) (intexp (0 1 1))) #t) (=/= ((_.0 numo))) (sym _.0))))

  (define rel-fact5
    `((lambda (f)
        ((f f) (intexp ,(build-num 5))))
      (lambda (f)
        (lambda (n)
          (if (zero? n)
              (intexp ,(build-num 1))
              (* n ((f f) (sub1 n))))))))

  (test-check "rel-fact5" 
              (run* (q) (eval-expo rel-fact5 '() q))
              `((intval ,(build-num 120))))

  (test-check "rel-fact5-backwards" 
              (run 1 (q)
                (eval-expo
                 `((lambda (f)
                     ((f ,q) (intexp ,(build-num 5))))
                   (lambda (f)
                     (lambda (n)
                       (if (zero? n)
                           (intexp ,(build-num 1))
                           (* n ((f f) (sub1 n)))))))
                 '()
                 `(intval ,(build-num 120))))
              `(f))
  )

(define (test-mk-long)
  (test-mk))

(module+ main
  (test-mk-long))

