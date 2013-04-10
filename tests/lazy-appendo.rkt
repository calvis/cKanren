#lang racket

(require "../ck.rkt" "../tree-unify.rkt" "../absento.rkt" "../neq.rkt")

(define-lazy-goal (syms* t out)
  (conde
   [(== t '())
    (== out '())]
   [(symbolo t)
    (== out `(,t))]
   [(fresh (a d a^ d^)
      (syms* a a^)
      (syms* d d^)
      (appendo a^ d^ out)
      (== t `(,a . ,d)))]))
  
(define-lazy-goal (appendo ls1 ls2 out)
  (conde
   ((== ls1 '()) 
    (== ls2 out))
   ((fresh (a d res)
      (appendo d ls2 res)
      (== ls1 `(,a . , d))
      (== out `(,a . ,res))))))

