#lang cKanren

(use-constraints cKanren/tree-unify)

(debug #:on)

;; (run* (q) ((== q 5)))
;; (run* (q) ((== q 5) 5))
;; (run* (q) ((== q 5) (== q 6)))
;; (run* (q) ((== q 5) 5 6))

;; (define fake-goal (lambda (x) "hi"))
;; (run* (q) (fake-goal 5))

(trace-define rembero 
  (lambda (x l s)
    (conde
     [#:name base-case
      (== l '()) (== s '())]
     [#:name found-x
      (fresh (d)
        (== l `(,x . ,d))
        (rembero x d s))]
     [#:name not-x
      (fresh (a d res)
        (== l `(,a . ,d))
;;         (=/= a x)
        (== s `(,a . ,res))
        (rembero x d res))])))

(run* (q) (rembero 'x '(x y) q) prt)
      
