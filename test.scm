(load "alphaK.ss")
(load "nnf.scm")
(load "alphaleantap.scm")

(import (alphaleantap) (nnf))

(define switch (make-parameter #t))

(import (alphaK))
;; (import (alphaK-records))

(import (only (mk) prt))

(print-gensym 'pretty/suffix)

(define-syntax pp
  (syntax-rules ()
    ((_ n axioms theorem)
     (begin
       (printf "Pelletier Problem ~s:\n" n)
       (printf "-----------------------------------\n")
       (let ((pr (do-prove-th axioms theorem))) pr)
       (printf "-----------------------------------\n\n")
       ))))

(define-syntax testit
  (syntax-rules ()
    ((_ num exp val)
     (begin
       (display "testing: ")
       (display num)
       (tester 'exp exp val)))))

(define tester
  (lambda (exp v val)
    (cond
      ((equal? v val) (display " okay") (newline))
      (else
        (error 'testit
          (format "\nexp: \n~a\nexpected: \n~a\ncomputed: \n~a"
            (with-output-to-string
              (lambda () (pretty-print exp)))
            (with-output-to-string
              (lambda () (pretty-print val)))
            (with-output-to-string
              (lambda () (pretty-print v)))))))))


;; Pelletier Problems

;; 1 - 5
;; Micah Linnemeier

(pp 1 '() '(<=> (=> p q) (=> (not q) (not p))))
(pp 2 '() '(=>  (not (not p)) p))
(pp 3 '() '(=> (not (=> p q)) (=> q p)))
(pp 4 '() '(<=> (=> (not p) q) (=> (not q) p)))
(pp 5 '() '(=> (=> (or p q) (or p r)) (or p (=> q r))))

;; 6 - 10
;; Adam Hinz

(pp 6 '() `(or p (not p)))
(pp 7 '() `(or p (not (not (not p)))))
(pp 8 '() `(=> (=> (=> p q) p) p))

(pp 9 '() 
  `(=> (and (or p q)
            (and
              (or (not p) q)
              (or p (not q))))
     (not (or (not p) (not q)))))

(pp 10
  `((=> q r)
    (=> r (and p q))
    (=> p (or q r)))
  `(<=> p q))

;; 11 - 15
;; Joe Near

(pp 11 '() '(<=> p p))
(pp 12 '() '(<=> (<=> (<=> p q) r) (<=> p (<=> q r))))
(pp 13 '() '(<=> (or p (and q r)) (and (or p q) (or p r))))
(pp 14 '() '(<=> (<=> p q) (and (or q (not p)) (or (not q) p))))
(pp 15 '() '(<=> (=> p q) (or (not p) q)))

;; 16 - 20
;; Micah Linnemeier

(pp 16 '() '(or (=> p q) (=> q p)))

(pp 17 '()
  `(<=> (=> (and p (=> q r)) s)
     (and (or (not p) (or q s)) (or (not p) (or (not r) s)))))

(if (switch)
    (testit 18
      (run 1 (q)
        (fresh-nom (y)
          (proveo
            `(forall ,(tie y
                        `(and (lit (pos (app f (var ,y))))
                              (lit (neg (app f (app g0.6 (var ,y))))))))
            `() `() `() q)))
      `((univ conj savefml savefml univ conj close)))
    (pp 18 '() `,(E y ,(A x (=> (f ,y) (f ,x))))))

(if (switch)
    (testit 19
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(forall ,(tie x
                        `(and (or (lit (neg (app p (app g0.6 (var ,x)))))
                                  (lit (pos (app q (app g1.7 (var ,x))))))
                              (and (lit (pos (app p (var ,x))))
                                   (lit (neg (app q (var ,x))))))))
            `() `() `() q)))
      `((univ
          conj
          split
          (savefml conj savefml savefml univ conj split (savefml conj close)
            (savefml conj close))
          (savefml conj savefml savefml univ conj split (savefml conj savefml close)
            (savefml conj savefml close)))))
    (pp 19 '()
      `,(E x ,(A y ,(A z (=>
                           (=> (p ,y) (q ,z))
                           (=> (p ,x) (q ,x))))))))

;; (pp 20 '() 
;;   `,(A x ,(A y ,(E z ,(A w 
;;                         (=>
;;                           (=> (and (p ,x) (q ,y))
;;                             (and (r ,z) (s ,w)))
;;                           ,(E x ,(E y
;;                                    (=>
;;                                      (and (p ,x) (q ,y))
;;                                      ,(E z
;;                                         (r ,z)))))))))))

;; 21 - 30
;; Micah Linnemeier

(if (switch)
    (testit 21
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (forall
                    ,(tie x
                       `(or (and (lit (neg (sym p)))
                                 (lit (pos (app f (var ,x)))))
                            (and (lit (pos (sym p)))
                                 (lit (neg (app f (var ,x))))))))
                  (and (or (lit (neg (sym p)))
                           (lit (pos (app f (app g2.8)))))
                       (or (lit (neg (app f (app g3.9))))
                           (lit (pos (sym p))))))
            `() `() `() q)))
      `((conj univ split
          (conj savefml savefml conj split (savefml split (close) (close))
            (savefml split (close) (close)))
          (conj savefml savefml conj split (close)
            (savefml
              split
              (savefml univ split (conj close) (conj savefml close))
              (savefml univ split (conj close) (conj savefml close)))))))
    (pp 21
      `(,(E x (=> p (f ,x))) ,(E x (=> (f ,x) p)))
      `,(E x (<=> p (f ,x)))))

(if (switch)
    (testit 22
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (forall
                    ,(tie x `(or (and (lit (pos (sym p)))
                                      (lit (pos (app f (var ,x)))))
                                 (and (lit (neg (sym p)))
                                      (lit (neg (app f (var ,x))))))))
                  (or (and (lit (neg (sym p)))
                           (forall
                             ,(tie x `(lit (pos (app f (var ,x)))))))
                      (and (lit (pos (sym p)))
                           (lit (neg (app f (app g0.53)))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (conj savefml savefml split (conj close)
            (conj savefml close))
          (conj savefml savefml split (conj savefml univ close)
            (conj close)))))
    (pp 22 '() `(=> ,(A x (<=> p (f ,x))) (<=> p ,(A x (f ,x))))))

(if (switch)
    (testit 23
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(or (and (and (lit (neg (sym p)))
                           (lit (neg (app f (app g1.60)))))
                      (or (lit (pos (sym p)))
                          (forall ,(tie x `(lit (pos (app f (var ,x))))))))
                 (and (forall ,(tie x `(or (lit (pos (sym p)))
                                           (lit (pos (app f (var ,x)))))))
                      (and (lit (neg (sym p)))
                           (lit (neg (app f (app g2.61)))))))
            `() `() `() q)))
      `((split
          (conj conj savefml savefml split (close) (univ close))
          (conj
            univ
            split
            (savefml conj close)
            (savefml conj savefml close)))))
    (pp 23 '() `(<=> ,(A x (or p (f ,x))) (or p ,(A x (f ,x))))))

(if (switch)
    (testit 24
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (forall ,(tie x `(or (lit (neg (app p (var ,x))))
                                       (lit (neg (app r (var ,x)))))))
                  (and (forall ,(tie x `(or (lit (neg (app s (var ,x))))
                                            (lit (neg (app q (var ,x)))))))
                       (and (forall
                              ,(tie x
                                 `(or (lit (neg (app p (var ,x))))
                                      (or (lit (pos (app q (var ,x))))
                                          (lit (pos (app r (var ,x))))))))
                            (and
                              (and
                                (lit (pos (app p (app g5.73))))
                                (forall
                                  ,(tie x `(lit (neg (app q (var ,x)))))))
                              (forall
                                ,(tie x
                                   `(or (and (lit (neg (app q (var ,x))))
                                             (lit (neg (app r (var ,x)))))
                                        (lit (pos (app s (var ,x)))))))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (savefml conj univ split
            (savefml conj univ split (savefml conj conj close)
              (split (savefml conj conj close) (savefml conj conj close)))
            (savefml conj univ split (savefml conj conj close)
              (split (close) (savefml conj conj close))))
          (savefml conj univ split
            (savefml conj univ split (savefml conj conj close)
              (split (savefml conj conj savefml univ close) (close)))
            (savefml conj univ split (savefml conj conj close)
              (split (close) (close)))))))

    (pp 24
      `((not ,(E x (and (s ,x) (q ,x))))
        ,(A x (=> (p ,x) (or (q ,x) (r ,x))))
        (not (=> ,(E x (p ,x)) ,(E x (q ,x))))
        ,(A x (=> (or (q ,x) (r ,x)) (s ,x))))
      `,(E x (and (p ,x) (r ,x)))))

(if (switch)

    (testit 25
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (forall ,(tie x `(or (lit (neg (app p (var ,x))))
                                       (lit (neg (app r (var ,x)))))))
                  (and (lit (pos (app p (app g6.80))))
                       (and (forall
                              ,(tie x `(or (lit (neg (app f (var ,x))))
                                           (and (lit (neg (app g (var ,x))))
                                                (lit (pos (app r (var ,x))))))))
                            (and (forall
                                   ,(tie x
                                      `(or (lit (neg (app p (var ,x))))
                                           (and (lit (pos (app g (var ,x))))
                                                (lit (pos (app f (var ,x))))))))
                                 (or (forall
                                       ,(tie x
                                          `(or (lit (neg (app p (var ,x))))
                                               (lit (pos (app r (var ,x)))))))
                                     (and (lit (pos (app p (app g7.81))))
                                          (lit (pos (app r (app g7.81))))))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (savefml conj close)
          (savefml conj savefml conj univ split
            (savefml conj univ split (close) (conj savefml close))
            (conj savefml close)))))

    (pp 25
      `(,(E x (p ,x))
        ,(A x (=> (f ,x) (and (not (g ,x)) (r ,x))))
        ,(A x (=> (p ,x) (and (g ,x) (f ,x))))
        (or ,(A x (=> (p ,x) (r ,x))) ,(E x (and (p ,x) (r ,x)))))
      `,(E x (and (p ,x) (r ,x)))))

;; Too slow
;; (pp 26
;;   `((<=> ,(E x (p ,x)) ,(E x (q ,x)))
;;     ,(A x ,(A y (=> (and (p ,x) (q ,y)) (<=> (r ,x) (s ,y))))))
;;   `(<=> ,(A x (=> (p ,x) (r ,x))) ,(A x (=> (q ,x) (s ,x)))))
  
(if (switch)
    (testit 27
      (run 1 (q)
        (fresh-nom (x)
          (proveo 
            `(and (and (lit (pos (app j (app g8.88))))
                       (lit (pos (app i (app g8.88)))))
                  (and (and (lit (pos (app f (app g9.89))))
                            (lit (neg (app g (app g9.89)))))
                       (and (forall
                              ,(tie x `(or (lit (neg (app f (var ,x))))
                                           (lit (pos (app h (var ,x)))))))
                            (and
                              (forall
                                ,(tie x `(or (or (lit (neg (app j (var ,x))))
                                                 (lit (neg (app i (var ,x)))))
                                             (lit (pos (app f (var ,x)))))))
                              (or (forall
                                    ,(tie x `(or (lit (neg (app h (var ,x))))
                                                 (lit (pos (app g (var ,x)))))))
                                  (forall
                                    ,(tie x
                                       `(or (lit (neg (app i (var ,x))))
                                            (lit (neg (app h (var ,x))))))))))))
            `() `() `() q)))
      `((conj conj savefml savefml conj conj savefml savefml conj univ
          split (close)
          (savefml conj univ split (split (close) (close))
            (savefml
              split
              (univ split (close) (close))
              (univ
                split
                (close)
                (savefml univ split (close) (close))))))))
    (pp 27
      `(,(E x (and (f ,x) (not (g ,x))))
        ,(A x (=> (f ,x) (h ,x)))
        ,(A x (=> (and (j ,x) (i ,x)) (f ,x)))
        (=> ,(E x (and (h ,x) (not (g ,x))))
          ,(A x (=> (i ,x) (not (h ,x))))))
      `,(A x (=> (j ,x) (not (i ,x))))))

(if (switch)
    (testit 28
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (and (and (lit (pos (app p (app g10.102))))
                            (lit (pos (app f (app g10.102)))))
                       (lit (neg (app g (app g10.102)))))
                  (and (forall
                         ,(tie x
                            `(or (lit (neg (app p (var ,x))))
                                 (forall
                                   ,(tie x `(lit (pos (app q (var ,x)))))))))
                       (and (or (and (lit (neg (app q (app g11.103))))
                                     (lit (neg (app r (app g11.103)))))
                                (and (lit (pos (app q (app g12.104))))
                                     (lit (pos (app s (app g12.104))))))
                            (or (forall ,(tie x `(lit (neg (app s (var ,x))))))
                                (forall
                                  ,(tie x
                                     `(or (lit (neg (app f (var ,x))))
                                          (lit (pos (app g (var ,x)))))))))))
            `() `() `() q)))
      `((conj conj conj savefml savefml savefml conj univ split (close)
          (univ savefml conj split (conj close)
            (conj savefml savefml split (univ close)
              (univ split (close) (close)))))))

    (pp 28
      `(,(A x (=> (p ,x) ,(A x (q ,x))))
        (=> ,(A x (or (q ,x) (r ,x))) ,(E x (and (q ,x) (s ,x))))
        (=> ,(E x (s ,x)) ,(A x (=> (f ,x) (g ,x)))))
      `,(A x (=> (and (p ,x) (f ,x)) (g ,x)))))

;; Too slow
;; (pp 29
;;   `((and ,(E x (f ,x)) ,(E x (g ,x))))
;;   `(<=>
;;      (and
;;        ,(A x (=> (f ,x) (h ,x)))
;;        ,(A x (=> (g ,x) (j ,x))))
;;      ,(A x ,(A y (=> (and (f ,x) (g ,y)) (and (h ,x) (j ,y)))))))

  



(if (switch)
    (testit 30
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (lit (neg (app i (app g13.111))))
                  (and (forall
                         ,(tie x `(or (and (lit (neg (app f (var ,x))))
                                           (lit (neg (app g (var ,x)))))
                                      (lit (neg (app h (var ,x)))))))
                       (forall
                         ,(tie x `(or (and (lit (pos (app g (var ,x))))
                                           (lit (pos (app i (var ,x)))))
                                      (and (lit (pos (app f (var ,x))))
                                           (lit (pos (app h (var ,x))))))))))
            `() `() `() q)))
      `((conj savefml conj univ split
          (conj savefml savefml univ split (conj close) (conj close))
          (savefml
            univ
            split
            (conj savefml close)
            (conj savefml close)))))

    (pp 30
      `(,(A x (=> (or (f ,x) (g ,x)) (not (h ,x))))
        ,(A x (=> (=> (g ,x) (not (i ,x))) (and (f ,x) (h ,x)))))
      `,(A x (i ,x))))

;; 31 - 40
;; Adam Hinz



(if (switch)
    (testit 31
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and
               (forall ,(tie x `(or (lit (neg (app i (var ,x))))
                                    (lit (neg (app j (var ,x)))))))
               (and (forall
                      ,(tie x `(or (lit (neg (app f (var ,x))))
                                   (and (lit (neg (app g (var ,x))))
                                        (lit (neg (app h (var ,x))))))))
                    (and (and (lit (pos (app i (app g14.118))))
                              (lit (pos (app f (app g14.118)))))
                         (forall ,(tie x `(or (lit (pos (app h (var ,x))))
                                              (lit (pos (app j (var ,x))))))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (savefml conj univ split (savefml conj conj close)
            (conj savefml savefml conj conj close))
          (savefml conj univ split (savefml conj conj savefml close)
            (conj savefml savefml conj conj savefml savefml univ split
              (close) (close))))))
    (pp 31
      `((not ,(E x (and (f ,x) (or (g ,x) (h ,x)))))
        ,(E x (and (i ,x) (f ,x)))
        ,(A x (=> (not (h ,x)) (j ,x))))
      `,(E x (and (i ,x) (j ,x)))))

(if (switch)
    (testit 32
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(and (and (and (lit (pos (app f (app g15.131))))
                            (lit (pos (app k (app g15.131)))))
                       (lit (neg (app j (app g15.131)))))
                  (and (forall
                         ,(tie x `(or (or (lit (neg (app f (var ,x))))
                                          (and (lit (neg (app g (var ,x))))
                                               (lit (neg (app h (var ,x))))))
                                      (lit (pos (app i (var ,x)))))))
                       (and (forall
                              ,(tie x `(or (or (lit (neg (app i (var ,x))))
                                               (lit (neg (app h (var ,x)))))
                                           (lit (pos (app j (var ,x)))))))
                            (forall
                              ,(tie x `(or (lit (neg (app k (var ,x))))
                                           (lit (pos (app h (var ,x))))))))))
            `() `() `() q)))
      `((conj conj conj savefml savefml savefml conj univ split
          (split
            (close)
            (conj savefml savefml conj univ split
              (split
                (savefml univ split (close) (close))
                (savefml univ split (close) (close)))
              (close)))
          (savefml conj univ split
            (split (close) (savefml univ split (close) (close)))
            (close)))))

    (pp 32
      `(,(A x (=> (and (f ,x) (or (g ,x) (h ,x))) (i ,x)))
        ,(A x (=> (and (i ,x) (h ,x)) (j ,x)))
        ,(A x (=> (k ,x) (h ,x))))
      `,(A x (=> (and (f ,x) (k ,x)) (j ,x)))))

;; (pp 33
;;   '()
;;   `(<=> ,(A x (=> (and (p a) (=> (p ,x) (p b))) (p c)))
;;      ,(A x (and (or (not (p a)) (or (p ,x) (p c)))
;;                 (or (not (p a)) (or (not (p b)) (p c)))))))

;; (pp 34
;;   '()
;;   `(<=>
;;      (<=> ,(E x ,(A y (<=> (p ,x) (p ,y))))
;;        (<=> ,(E x (q ,x)) ,(A y (q ,y))))
;;      (<=> ,(E x ,(A y (<=> (q ,x) (q ,y))))
;;        (<=> ,(E x (p ,x)) ,(A y (p ,y))))))

;; (testit 34
;;   (run 1 (q)
;;     (fresh-nom (x y)
;;       (proveo `(or (and (or (and (forall ,(tie x `(or (and (lit (neg (app p (var ,x)))) (lit (pos (app p (app g41.184 (var ,x)))))) (and (lit (pos (app p (var ,x)))) (lit (neg (app p (app g41.184 (var ,x))))))))) (or (and (lit (pos (app q (app g42.185)))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (lit (neg (app q (app g43.186))))))) (and (forall ,(tie y `(or (and (lit (pos (app p (app g44.187)))) (lit (pos (app p (var ,y))))) (and (lit (neg (app p (app g44.187)))) (lit (neg (app p (var ,y)))))))) (or (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (lit (pos (app q (app g45.188)))) (lit (neg (app q (app g46.189)))))))) (or (and (forall ,(tie y `(or (and (lit (pos (app q (app g47.190)))) (lit (pos (app q (var ,y))))) (and (lit (neg (app q (app g47.190)))) (lit (neg (app q (var ,y)))))))) (or (and (lit (pos (app p (app g48.191)))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (lit (neg (app p (app g49.192))))))) (and (forall ,(tie x `(or (and (lit (neg (app q (var ,x)))) (lit (pos (app q (app g50.193 (var ,x)))))) (and (lit (pos (app q (var ,x)))) (lit (neg (app q (app g50.193 (var ,x))))))))) (or (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (lit (pos (app p (app g51.194)))) (lit (neg (app p (app g52.195))))))))) (and (or (and (forall ,(tie y `(or (and (lit (pos (app p (app g53.196)))) (lit (pos (app p (var ,y))))) (and (lit (neg (app p (app g53.196)))) (lit (neg (app p (var ,y)))))))) (or (and (lit (pos (app q (app g54.197)))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (lit (neg (app q (app g55.198))))))) (and (forall ,(tie x `(or (and (lit (neg (app p (var ,x)))) (lit (pos (app p (app g56.199 (var ,x)))))) (and (lit (pos (app p (var ,x)))) (lit (neg (app p (app g56.199 (var ,x))))))))) (or (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (lit (pos (app q (app g57.200)))) (lit (neg (app q (app g58.201)))))))) (or (and (forall ,(tie x `(or (and (lit (neg (app q (var ,x)))) (lit (pos (app q (app g59.202 (var ,x)))))) (and (lit (pos (app q (var ,x)))) (lit (neg (app q (app g59.202 (var ,x))))))))) (or (and (lit (pos (app p (app g60.203)))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (lit (neg (app p (app g61.204))))))) (and (forall ,(tie y `(or (and (lit (pos (app q (app g62.205)))) (lit (pos (app q (var ,y))))) (and (lit (neg (app q (app g62.205)))) (lit (neg (app q (var ,y)))))))) (or (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (lit (pos (app p (app g63.206)))) (lit (neg (app p (app g64.207)))))))))) `() `() `() q)))
;;   `(nofail))

;; Too slow
;; (pp 35
;;   '()
;;   `,(E x ,(E y (=> (p ,x ,y) ,(A x ,(A y (p ,x ,y)))))))

;; Too slow
;; (pp 36
;;   `(,(A x ,(E y (f ,x ,y)))
;;     ,(A x ,(E y (g ,x ,y)))
;;     ,(A x ,(A y (=> (or (f ,x ,y) (g ,x ,y))
;;                   ,(A z (=> (or (f ,y ,z) (g ,y ,z)) (h ,x ,z)))))))
;;   `,(A x ,(E y (h ,x ,y))))


;; Too slow
;; (pp 37
;;   `(,(A z ,(E w ,(A x ,(E y (and (=> (p ,x ,z) (p ,y ,w))
;;                                  (and (p ,y ,z)
;;                                       (=> (p ,y ,w) ,(E u (q ,u ,w)))))))))
;;     ,(A x ,(A z (=> (not (p ,x ,z)) ,(E y (q ,y ,z)))))
;;     (=> ,(E x ,(E y (q ,x ,y))) ,(A x (r ,x ,x))))
;;   `,(A x ,(E y (r ,x ,y))))

;; Too slow
;; (pp 38
;;   '()
;;   `(<=> ,(A x (=> (and (p a) (=> (p ,x) ,(E y (and (p ,y) (r ,x ,y)))))
;;                 ,(E z ,(E w (and (p ,z) (and (r ,x ,w) (r ,w ,z)))))))
;;      ,(A x (and
;;              (or (not (p a)) (or (p ,x) ,(E z ,(E w (and (p ,z)
;;                                                          (and (r ,x ,w)
;;                                                               (r ,w ,z)))))))
;;              (or (not (p a))
;;                  (or (not ,(E y (and (p ,y) (r ,x ,y))))
;;                      ,(E z ,(E w (and (p ,z)
;;                                       (and (r ,x ,w)
;;                                            (r ,w ,z)))))))))))

(if (switch)
    (testit 39
      (run 1 (q)
        (fresh-nom (y)
          (proveo 
            `(forall ,(tie y `(or (and (lit (pos (app f (var ,y) (app g0.6)))) (lit (neg (app f (var ,y) (var ,y))))) (and (lit (neg (app f (var ,y) (app g0.6)))) (lit (pos (app f (var ,y) (var ,y))))))))
            `() `() `() q)
          prt))
      `((conj
          univ
          split
          (savefml conj univ conj split (savefml conj savefml savefml conj close)
            (conj savefml savefml conj savefml savefml conj close))
          (savefml conj univ conj split (close)
            (conj savefml savefml conj savefml savefml conj savefml univ split (close)
              (close))))))

    (pp 39
      '()
      `(not ,(E x ,(A y (<=> (f ,y ,x) (not (f ,y ,y))))))))

;; Too slow
;; (pp 40
;;   '()
;;   `(=> ,(E y ,(A x (<=> (f ,x ,y) (f ,x ,x))))
;;      (not ,(A x ,(E y ,(A z (<=> (f ,z ,y) (not (f ,z ,x)))))))))

;; (Assigned to Joe Near)

;; (pp 41
;;   `(,(A z ,(E y ,(A x (<=> (F ,x ,y) (and (F ,x ,z) (not (F ,x ,x))))))))
;;   `(not ,(E z ,(A x (F ,x ,z)))))

;; (testit 41
;;   (run 1 (q)
;;     (fresh-nom (x z)
;;       (proveo `(and (forall ,(tie x `(lit (pos (app F (var ,x) (app g0.12)))))) (forall ,(tie z `(forall ,(tie x `(or (and (lit (pos (app F (var ,x) (app g1.13 (var ,z))))) (and (lit (pos (app F (var ,x) (var ,z)))) (lit (neg (app F (var ,x) (var ,x)))))) (and (lit (neg (app F (var ,x) (app g1.13 (var ,z))))) (or (lit (neg (app F (var ,x) (var ,z)))) (lit (pos (app F (var ,x) (var ,x))))))))))))
;;         `() `() `() q)))
;;   `((conj univ savefml univ univ split
;;       (conj savefml conj savefml close)
;;       (conj savefml split (close) (close)))))

;; Too slow
;; (pp 42
;;   '()
;;   `(not ,(E y ,(A x (<=> (F ,x ,y) (not ,(E z (and (F ,x ,z) (F ,z ,x)))))))))

;; Too slow
;; (pp 43
;;   `(,(A x ,(A y (<=> (Q ,x ,y) ,(A z (<=> (F ,z ,x) (F ,z ,y)))))))
;;   `,(A x ,(A y (<=> (Q ,x ,y) (Q ,y ,x)))))

(if (switch)
    (testit 44
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (forall ,(tie x `(or (lit (neg (app J (var ,x)))) (lit (pos (app F (var ,x))))))) (and (forall ,(tie x `(and (or (lit (neg (app F (var ,x)))) (and (lit (pos (app G (app g2.20 (var ,x))))) (lit (pos (app H (var ,x) (app g2.20 (var ,x))))))) (and (lit (pos (app G (app g3.21 (var ,x))))) (lit (neg (app H (var ,x) (app g3.21 (var ,x))))))))) (and (lit (pos (app J (app g4.22)))) (forall ,(tie y `(or (lit (neg (app G (var ,y)))) (lit (pos (app H (app g4.22) (var ,y))))))))))
            `() `() `() q)))
      `(nofail))

    (pp 44
      `(,(A x (and (=> (F ,x) ,(E y (and (G ,y) (H ,x ,y))))
                   ,(E y (and (G ,y) (not (H ,x ,y))))))
        ,(E x (and (J ,x) ,(A y (=> (G ,y) (H ,x ,y))))))
      `,(E x (and (J ,x) (not (F ,x))))))

(pp 45
  `(,(A x (and (F ,x) ,(A y (=> (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))
                              ,(A y (and (G ,y) (=> (H ,x ,y) (K ,y))))))))
    (not ,(E y (and (L ,y) (K ,y))))
    ,(E x (and (and (F ,x) ,(A y (=> (H ,x ,y) (L ,y))))
               ,(A y (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))))))
  `,(E x (and (F ,x) (not ,(E y (and (G ,y) (H ,x ,y)))))))

'(conj
   univ
   split
   (savefml conj univ conj close)
   (conj savefml savefml conj univ conj savefml univ split
     (split
       (close)
       (conj savefml savefml conj univ split
         (savefml conj conj savefml univ split (close) (close))
         (savefml conj conj savefml univ split (close)
           (savefml univ conj savefml split (close) (close)))))
     (univ conj savefml split (close)
       (savefml conj univ split
         (savefml conj conj savefml univ split (close) (close)) (close)))))

(pp 46
  `(,(A x (=> (and (F ,x) ,(A y (=> (and (F ,y) (H ,y ,x))
                                  (G ,y))))
            (G ,x)))
    (=> ,(E x (and (F ,x) (not (G ,x))))
      ,(E x (and (F ,x) (and (not (G ,x))
                             ,(A y (=> (and (F ,y) (not (G ,y))) (J ,x ,y)))))))
    ,(A x ,(A y (=> (and (F ,x) (and (F ,y) (H ,x ,y))) (not (J ,y ,x))))))
  `,(A x (=> (F ,x) (G ,x))))

'(conj conj savefml savefml conj univ split
   (split
     (savefml conj split (univ split (close) (close)) (conj close))
     (conj conj savefml savefml savefml conj split (univ split (close) (close))
       (conj savefml conj savefml univ split (split (close) (close))
         (savefml univ univ split (split (close) (split (close) (close)))
           (close)))))
   (savefml conj split (univ split (close) (close)) (conj savefml conj close)))

(printf "all done!\n")


