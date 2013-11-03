#lang racket

(require
 "../ck.rkt" 
 "../tree-unify.rkt" 
 "../attributes.rkt" 
 "../neq.rkt"
 "../tester.rkt"
 (for-syntax "../ck.rkt"))

;; (search-strategy 'bfs)
;; (begin-for-syntax
 ;; (search-strategy 'dfs)
;;)

(define ;;-lazy-goal 
  (syms* t out)
  (conde
   [(== t '())
    (== out '())]
   [(symbol t)
    (== out `(,t))]
   [(fresh (a d a^ d^)
      (appendo a^ d^ out)
      (syms* a a^)
      (syms* d d^)
      (== t `(,a . ,d)))]))
  
(define ;;-lazy-goal 
  (appendo ls1 ls2 out)
  (conde
   [(== ls1 '()) 
    (== ls2 out)]
   [(fresh (a d res)
      (appendo d ls2 res)
      (== ls1 `(,a . , d))
      (== out `(,a . ,res)))]))

(module+ test
  (test "appendo"
        (run* (q) (appendo '(a b) '(c d) q))
        '((a b c d)))
  
  (test "symb* 1"
        (run* (q) (syms* '(a) q))
        '((a)))
  
  (test "symb* 2"
        (run* (q) (syms* '(a (b)) q))
        '((a b)))
  
  (test "symb* 3"
        (run* (q) (syms* '((a (b) c)) q))
        '((a b c))))
