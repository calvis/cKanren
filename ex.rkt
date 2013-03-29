#lang s-exp "ck-lang.rkt"
(use-constraints "tree-unify.rkt" "neq.rkt")

;; (run* (q) ((== q 5)))
;; (run* (q) ((== q 5) 5))
;; (run* (q) ((== q 5) (== q 6)))
;; (run* (q) ((== q 5) 5 6))

;; (define fake-goal (lambda (x) "hi"))
;; (run* (q) (fake-goal 5))

(trace-define rembero 
  (lambda (x l s)
    (conde
     ((== l '()) (== s '()))
     ((fresh (d)
        (== l `(,x . ,d))
        (rembero x d s)))
     ((fresh (a d res)
        (== l `(,a . ,d))
;;         (=/= a x)
        (== s `(,a . ,res))
        (rembero x d res))))))

(run* (q) (rembero 'x '(x y) q) prt)
      
