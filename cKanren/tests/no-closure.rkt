#lang racket

(require
 "../ck.rkt"
 "../absento.rkt"
 "../tree-unify.rkt"
 "../tester.rkt")
(provide test-no-closure test-no-closure-long)

(define (test-no-closure)
  (test-check "absento 'closure-1a"
              (run 1 (q) (absento 'closure q) (== q 'closure))
              '())

  (test-check "absento 'closure-1b"
              (run 1 (q) (== q 'closure) (absento 'closure q))
              '())

  (test-check "absento 'closure-2a"
              (run 1 (q) (fresh (a d) (== q 'closure) (absento 'closure q)))
              '())

  (test-check "absento 'closure-2b"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== q 'closure)))
              '())

  (test-check "absento 'closure-3a"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== `(,a . ,d) q)))
              '(((_.0 . _.1) (absento (closure _.0) (closure _.1)))))


  (test-check "absento 'closure-3b"
              (run 1 (q) (fresh (a d) (== `(,a . ,d) q) (absento 'closure q)))  
              '(((_.0 . _.1) (absento (closure _.0) (closure _.1)))))


  (test-check "absento 'closure-4a"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure a)))
              '())

  (test-check "absento 'closure-4b"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== 'closure a) (== `(,a . ,d) q)))
              '())

  (test-check "absento 'closure-4c"
              (run 1 (q) (fresh (a d) (== 'closure a) (absento 'closure q) (== `(,a . ,d) q)))
              '())

  (test-check "absento 'closure-4d"
              (run 1 (q) (fresh (a d) (== 'closure a) (== `(,a . ,d) q) (absento 'closure q)))
              '())

  (test-check "absento 'closure-5a"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== `(,a . ,d) q) (== 'closure d)))
              '())

  (test-check "absento 'closure-5b"
              (run 1 (q) (fresh (a d) (absento 'closure q) (== 'closure d) (== `(,a . ,d) q)))
              '())

  (test-check "absento 'closure-5c"
              (run 1 (q) (fresh (a d) (== 'closure d) (absento 'closure q) (== `(,a . ,d) q)))
              '())

  (test-check "absento 'closure-5d"
              (run 1 (q) (fresh (a d) (== 'closure d) (== `(,a . ,d) q) (absento 'closure q)))
              '())

  (test-check "absento 'closure-6"
              (run 1 (q)
                (== `(3 (closure x (x x) ((y . 7))) #t) q)
                (absento 'closure q))
              '())
)

(define (test-no-closure-long)
  (test-no-closure))

(module+ main
  (test-no-closure-long))
