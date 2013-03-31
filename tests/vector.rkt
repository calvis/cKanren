#lang s-exp "../ck-lang.rkt"

(require racket "tester.rkt")

(module+ main
  (use-constraints "../tree-unify.rkt")

  (test-check "1" 
              (run* (q) 
                (fresh (x y)
                  (== q (vector x y))
                  (== y 2)))
              `(#(_.0 2)))

  (test-check "2"
              (run* (q)
                (fresh (x y)
                  (== (vector x 2) (vector 1 y))
                  (== q `(,x ,y))))
              `((1 2))))
