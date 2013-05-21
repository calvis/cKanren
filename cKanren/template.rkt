#lang racket

(require "ck.rkt" "tree-unify.rkt")

(provide templateo)

(define (templateo t x)
  (goal-construct (template t x)))

(define (template t x)
  (lambdam@ (a : s c)
    (let ([t (walk t s)]
          [x (walk x s)])
      (cond
       [(pair? t)
        (let ([first (var 'a)]
              [rest (var 'd)])
          (bindm a
            (composem
             (==-c x `(,first . ,rest))
             (template (car t) first)
             (template (cdr t) rest))))]
       [(or (not (var? t))
            (let ([rands (map oc-rands (filter/rator 'template c))])
              (member (list x t) rands)))
        (bindm a (==-c t x))]
       [else (bindm a (update-c (build-oc template t x)))]))))

(module+ test
  (require "tester.rkt")
  (test "1" (run* (q) (templateo q q)) '(_.0))
  (test "2" (run* (q) (templateo 5 q)) '(5))
  (test "3" (run* (q) (templateo q 5) (templateo q 6)) '(_.0))
  (test "4" 
        (run* (q) 
          (fresh (x y)
            (templateo q 5)
            (== `(,x ,y) q)))
        '())
  (test "5"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q `(,x . ,y))))
        '((_.0 . _.1)))
  (test "6"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4 5 6 7))
            (== q 5)))
        '())
  (test "7"
        (run* (q)
          (fresh (x y)
            (templateo q `(1 2))
            (templateo q `(3 4))))
        '???))

