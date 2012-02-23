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
       (printf "Pelletier Problem ~s\n" n)
       (let ((pr (do-prove-th axioms theorem))) pr)))))

(define-syntax testit
  (syntax-rules ()
    ((_ num exp val)
     (begin
       (printf "Pelletier Problem ~s\n" num)
       (tester 'exp exp val)))))

(define tester
  (lambda (exp v val)
    (cond
      ((equal? v val))
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

(pp 1 '() '(<=> (=> p q) (=> (not q) (not p))))
(pp 2 '() '(=>  (not (not p)) p))
(pp 3 '() '(=> (not (=> p q)) (=> q p)))
(pp 4 '() '(<=> (=> (not p) q) (=> (not q) p)))
(pp 5 '() '(=> (=> (or p q) (or p r)) (or p (=> q r))))
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

(pp 11 '() '(<=> p p))
(pp 12 '() '(<=> (<=> (<=> p q) r) (<=> p (<=> q r))))
(pp 13 '() '(<=> (or p (and q r)) (and (or p q) (or p r))))
(pp 14 '() '(<=> (<=> p q) (and (or q (not p)) (or (not q) p))))
(pp 15 '() '(<=> (=> p q) (or (not p) q)))
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

(if (switch)
    (testit 20
      (run 1 (q)
        (fresh-nom (x y w z)
          (proveo
            `(forall ,(tie z `(and (or (or (lit (neg (app p (app g3.12)))) (lit (neg (app q (app g4.13))))) (and (lit (pos (app r (var ,z)))) (lit (pos (app s (app g5.14 (var ,z))))))) (forall ,(tie x `(forall ,(tie y `(and (and (lit (pos (app p (var ,x)))) (lit (pos (app q (var ,y))))) (forall ,(tie z `(lit (neg (app r (var ,z))))))))))))))
            `() `() `() q)))
      `((univ
          conj
          split
          (split
            (savefml univ univ conj conj close)
            (savefml univ univ conj conj savefml close))
          (conj savefml savefml univ univ conj conj savefml savefml univ close))))
    (pp 20 '() 
      `,(A x ,(A y ,(E z ,(A w 
                            (=>
                              (=> (and (p ,x) (q ,y))
                                (and (r ,z) (s ,w)))
                              ,(E x ,(E y
                                       (=>
                                         (and (p ,x) (q ,y))
                                         ,(E z
                                            (r ,z))))))))))))

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

(if (switch)
    (testit 26
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (or (and (and (lit (pos (app p (app g14.23)))) (lit (neg (app r (app g14.23))))) (forall ,(tie x `(or (lit (neg (app q (var ,x)))) (lit (pos (app s (var ,x)))))))) (and (forall ,(tie x `(or (lit (neg (app p (var ,x)))) (lit (pos (app r (var ,x))))))) (and (lit (pos (app q (app g15.24)))) (lit (neg (app s (app g15.24))))))) (and (or (and (lit (pos (app p (app g16.25)))) (lit (pos (app q (app g17.26))))) (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (forall ,(tie x `(lit (neg (app q (var ,x)))))))) (forall ,(tie x `(forall ,(tie y `(or (or (lit (neg (app p (var ,x)))) (lit (neg (app q (var ,y))))) (or (and (lit (pos (app r (var ,x)))) (lit (pos (app s (var ,y))))) (and (lit (neg (app r (var ,x)))) (lit (neg (app s (var ,y)))))))))))))
            `() `() `() q)))
      `((conj
          split
          (conj conj savefml savefml univ split
            (savefml conj split (conj savefml close) (conj univ close))
            (savefml
              conj
              split
              (conj savefml savefml univ univ split (split (close) (close))
                (split (conj close) (conj savefml close)))
              (conj univ close)))
          (conj
            univ
            split
            (savefml conj savefml savefml conj split (conj close)
              (conj univ savefml univ close))
            (savefml conj savefml savefml conj split
              (conj savefml savefml univ univ split (split (close) (close))
                (split (conj savefml close) (conj close)))
              (conj univ savefml univ close))))))
    (pp 26
      `((<=> ,(E x (p ,x)) ,(E x (q ,x)))
        ,(A x ,(A y (=> (and (p ,x) (q ,y)) (<=> (r ,x) (s ,y))))))
      `(<=> ,(A x (=> (p ,x) (r ,x))) ,(A x (=> (q ,x) (s ,x))))))

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

(if (switch)
    (testit 29
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (or (and (or (and (lit (pos (app f (app g23.32)))) (lit (neg (app h (app g23.32))))) (and (lit (pos (app g (app g24.33)))) (lit (neg (app j (app g24.33)))))) (forall ,(tie x `(forall ,(tie y `(or (or (lit (neg (app f (var ,x)))) (lit (neg (app g (var ,y))))) (and (lit (pos (app h (var ,x)))) (lit (pos (app j (var ,y))))))))))) (and (and (forall ,(tie x `(or (lit (neg (app f (var ,x)))) (lit (pos (app h (var ,x))))))) (forall ,(tie x `(or (lit (neg (app g (var ,x)))) (lit (pos (app j (var ,x)))))))) (and (and (lit (pos (app f (app g25.34)))) (lit (pos (app g (app g26.35))))) (or (lit (neg (app h (app g25.34)))) (lit (neg (app j (app g26.35)))))))) (and (lit (pos (app f (app g27.36)))) (lit (pos (app g (app g28.37))))))
            `() `() `() q)))
      `((conj
          split
          (conj
            split
            (conj savefml savefml univ univ split
              (split (close) (savefml conj savefml close)) (conj close))
            (conj savefml savefml univ univ split (split (savefml conj close) (close))
              (conj savefml close)))
          (conj conj univ split
            (savefml univ split (savefml conj conj close) (savefml conj conj close))
            (savefml
              univ
              split
              (savefml conj conj savefml close)
              (savefml conj conj savefml savefml split (close) (close)))))))
    (pp 29
      `((and ,(E x (f ,x)) ,(E x (g ,x))))
      `(<=>
         (and
           ,(A x (=> (f ,x) (h ,x)))
           ,(A x (=> (g ,x) (j ,x))))
         ,(A x ,(A y (=> (and (f ,x) (g ,y)) (and (h ,x) (j ,y))))))))

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

(if (switch)
    (testit 33
      (run 1 (q)
        (fresh-nom (x)
          (proveo
            `(or (and (and (and (lit (pos (app p (sym a)))) (or (lit (neg (app p (app g32.41)))) (lit (pos (app p (sym b)))))) (lit (neg (app p (sym c))))) (forall ,(tie x `(and (or (lit (neg (app p (sym a)))) (or (lit (pos (app p (var ,x)))) (lit (pos (app p (sym c)))))) (or (lit (neg (app p (sym a)))) (or (lit (neg (app p (sym b)))) (lit (pos (app p (sym c)))))))))) (and (forall ,(tie x `(or (or (lit (neg (app p (sym a)))) (and (lit (pos (app p (var ,x)))) (lit (neg (app p (sym b)))))) (lit (pos (app p (sym c))))))) (or (and (lit (pos (app p (sym a)))) (and (lit (neg (app p (app g33.42)))) (lit (neg (app p (sym c)))))) (and (lit (pos (app p (sym a)))) (and (lit (pos (app p (sym b)))) (lit (neg (app p (sym c)))))))))
            `() `() `() q)))
      `((split
          (conj conj conj savefml split
            (savefml savefml univ conj split (close) (split (close) (close)))
            (savefml savefml univ conj split (close) (split (close) (close))))
          (conj
            univ
            split
            (split (savefml split (conj close) (conj close)) (conj savefml close))
            (savefml
              split
              (conj savefml conj savefml close)
              (conj savefml conj savefml close))))))
    (pp 33
      '()
      `(<=> ,(A x (=> (and (p a) (=> (p ,x) (p b))) (p c)))
         ,(A x (and (or (not (p a)) (or (p ,x) (p c)))
                    (or (not (p a)) (or (not (p b)) (p c))))))))

;; Diverges
;; (if (switch)
;;     (testit 34
;;       (run 1 (q)
;;         (fresh-nom (x y z)
;;           (proveo
;;             `(or (and (or (and (forall ,(tie x `(or (and (lit (neg (app p (var ,x)))) (lit (pos (app p (app g34.43 (var ,x)))))) (and (lit (pos (app p (var ,x)))) (lit (neg (app p (app g34.43 (var ,x))))))))) (or (and (lit (pos (app q (app g35.44)))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (lit (neg (app q (app g36.45))))))) (and (forall ,(tie y `(or (and (lit (pos (app p (app g37.46)))) (lit (pos (app p (var ,y))))) (and (lit (neg (app p (app g37.46)))) (lit (neg (app p (var ,y)))))))) (or (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (lit (pos (app q (app g38.47)))) (lit (neg (app q (app g39.48)))))))) (or (and (forall ,(tie y `(or (and (lit (pos (app q (app g40.49)))) (lit (pos (app q (var ,y))))) (and (lit (neg (app q (app g40.49)))) (lit (neg (app q (var ,y)))))))) (or (and (lit (pos (app p (app g41.50)))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (lit (neg (app p (app g42.51))))))) (and (forall ,(tie x `(or (and (lit (neg (app q (var ,x)))) (lit (pos (app q (app g43.52 (var ,x)))))) (and (lit (pos (app q (var ,x)))) (lit (neg (app q (app g43.52 (var ,x))))))))) (or (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (lit (pos (app p (app g44.53)))) (lit (neg (app p (app g45.54))))))))) (and (or (and (forall ,(tie y `(or (and (lit (pos (app p (app g46.55)))) (lit (pos (app p (var ,y))))) (and (lit (neg (app p (app g46.55)))) (lit (neg (app p (var ,y)))))))) (or (and (lit (pos (app q (app g47.56)))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (lit (neg (app q (app g48.57))))))) (and (forall ,(tie x `(or (and (lit (neg (app p (var ,x)))) (lit (pos (app p (app g49.58 (var ,x)))))) (and (lit (pos (app p (var ,x)))) (lit (neg (app p (app g49.58 (var ,x))))))))) (or (and (forall ,(tie x `(lit (neg (app q (var ,x)))))) (forall ,(tie y `(lit (pos (app q (var ,y))))))) (and (lit (pos (app q (app g50.59)))) (lit (neg (app q (app g51.60)))))))) (or (and (forall ,(tie x `(or (and (lit (neg (app q (var ,x)))) (lit (pos (app q (app g52.61 (var ,x)))))) (and (lit (pos (app q (var ,x)))) (lit (neg (app q (app g52.61 (var ,x))))))))) (or (and (lit (pos (app p (app g53.62)))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (lit (neg (app p (app g54.63))))))) (and (forall ,(tie y `(or (and (lit (pos (app q (app g55.64)))) (lit (pos (app q (var ,y))))) (and (lit (neg (app q (app g55.64)))) (lit (neg (app q (var ,y)))))))) (or (and (forall ,(tie x `(lit (neg (app p (var ,x)))))) (forall ,(tie y `(lit (pos (app p (var ,y))))))) (and (lit (pos (app p (app g56.65)))) (lit (neg (app p (app g57.66))))))))))
;;             `() `() `() q)))
;;       (split
;;         (conj
;;           split
;;           (conj
;;             univ
;;             split
;;             (conj savefml savefml split
;;               (conj savefml univ savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml savefml split (conj close) (conj univ close))
;;                   (conj savefml close))
;;                 (conj univ split (conj close) (conj savefml close)))
;;               (conj univ savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj close)
;;                   (conj savefml savefml split (conj close) (conj univ close)))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml savefml split (conj univ close)
;;                     (conj savefml savefml univ split (conj close)
;;                       (conj savefml savefml univ close)))
;;                   (conj close))))
;;             (conj savefml savefml split
;;               (conj savefml univ savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml savefml split (conj savefml univ close)
;;                     (conj univ close))
;;                   (conj savefml close))
;;                 (conj univ split (conj close) (conj savefml close)))
;;               (conj univ savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj savefml univ close)
;;                     (conj univ close)))
;;                 (conj univ split (conj savefml close) (conj close)))))
;;           (conj
;;             univ
;;             split
;;             (conj savefml savefml split (conj univ savefml univ close)
;;               (conj savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split
;;                     (conj savefml univ savefml univ split
;;                       (conj savefml savefml univ split (conj close)
;;                         (conj savefml close))
;;                       (conj close))
;;                     (conj univ close)))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj close)
;;                   (conj savefml savefml split (conj univ close)
;;                     (conj savefml close)))))
;;             (conj savefml savefml split (conj univ savefml univ close)
;;               (conj savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj savefml univ close)
;;                     (conj univ savefml savefml univ split (conj close)
;;                       (conj savefml savefml univ split (conj close)
;;                         (conj savefml close)))))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj close)
;;                   (conj savefml savefml split (conj univ savefml univ close)
;;                     (conj savefml savefml univ split (conj close)
;;                       (conj savefml close))))))))
;;         (conj
;;           split
;;           (conj
;;             univ
;;             split
;;             (conj savefml savefml split
;;               (conj savefml univ savefml split
;;                 (conj univ split (conj close) (conj savefml close))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml savefml split (conj univ close) (conj savefml close))
;;                   (conj savefml close)))
;;               (conj univ savefml savefml split
;;                 (conj univ split (conj savefml close) (conj close))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj univ close)
;;                     (conj savefml close)))))
;;             (conj savefml savefml split
;;               (conj savefml univ savefml split
;;                 (conj univ split (conj close) (conj savefml close))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml savefml split (conj univ savefml univ close)
;;                     (conj savefml savefml univ split (conj close)
;;                       (conj savefml close)))
;;                   (conj savefml close)))
;;               (conj univ savefml savefml split
;;                 (conj univ split (conj savefml close) (conj close))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj univ savefml univ close)
;;                     (conj savefml savefml univ split (conj close)
;;                       (conj savefml close)))))))
;;           (conj
;;             univ
;;             split
;;             (conj savefml savefml split (conj univ savefml univ close)
;;               (conj savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj close)
;;                   (conj savefml savefml split (conj savefml univ close)
;;                     (conj univ close)))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj univ close) (conj close)))))
;;             (conj savefml savefml split (conj univ savefml univ close)
;;               (conj savefml savefml split
;;                 (conj
;;                   univ
;;                   split
;;                   (conj close)
;;                   (conj savefml savefml split (conj savefml univ close)
;;                     (conj univ close)))
;;                 (conj
;;                   univ
;;                   split
;;                   (conj savefml close)
;;                   (conj savefml savefml split (conj univ close)
;;                     (conj savefml savefml univ split (conj close)
;;                       (conj savefml savefml univ split (conj close)
;;                         (conj savefml close)))))))))))
;;     (pp 34
;;       '()
;;       `(<=>
;;          (<=> ,(E x ,(A y (<=> (p ,x) (p ,y))))
;;            (<=> ,(E x (q ,x)) ,(A y (q ,y))))
;;          (<=> ,(E x ,(A y (<=> (q ,x) (q ,y))))
;;            (<=> ,(E x (p ,x)) ,(A y (p ,y)))))))

(if (switch)
    (testit 35
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(forall ,(tie x `(forall ,(tie y `(and (lit (pos (app p (var ,x) (var ,y)))) (lit (neg (app p (app g58.67) (app g59.68)))))))))
            `() `() `() q)))
      `((univ univ conj savefml close)))
    (pp 35
      '()
      `,(E x ,(E y (=> (p ,x ,y) ,(A x ,(A y (p ,x ,y))))))))

(if (switch)
    (testit 36
      (run 1 (q)
        (fresh-nom (x y z)
          (proveo
            `(and (forall ,(tie y `(lit (neg (app h (app g60.69) (var ,y)))))) (and (forall ,(tie x `(lit (pos (app f (var ,x) (app g61.70 (var ,x))))))) (and (forall ,(tie x `(lit (pos (app g (var ,x) (app g62.71 (var ,x))))))) (forall ,(tie x `(forall ,(tie y `(or (and (lit (neg (app f (var ,x) (var ,y)))) (lit (neg (app g (var ,x) (var ,y))))) (forall ,(tie z `(or (and (lit (neg (app f (var ,y) (var ,z)))) (lit (neg (app g (var ,y) (var ,z))))) (lit (pos (app h (var ,x) (var ,z)))))))))))))))
            `() `() `() q)))
      `((conj univ savefml conj univ savefml conj univ savefml univ univ split
          (conj close) (univ split (conj savefml close) (close)))))
    (pp 36
      `(,(A x ,(E y (f ,x ,y)))
        ,(A x ,(E y (g ,x ,y)))
        ,(A x ,(A y (=> (or (f ,x ,y) (g ,x ,y))
                      ,(A z (=> (or (f ,y ,z) (g ,y ,z)) (h ,x ,z)))))))
      `,(A x ,(E y (h ,x ,y)))))

(if (switch)
    (testit 37
      (run 1 (q)
        (fresh-nom (x y z)
          (proveo
            `(and (forall ,(tie y `(lit (neg (app r (app g63.72) (var ,y)))))) (and (forall ,(tie z `(forall ,(tie x `(and (or (lit (neg (app p (var ,x) (var ,z)))) (lit (pos (app p (app g64.73 (var ,x) (var ,z)) (app g65.74 (var ,z)))))) (and (lit (pos (app p (app g64.73 (var ,x) (var ,z)) (var ,z)))) (or (lit (neg (app p (app g64.73 (var ,x) (var ,z)) (app g65.74 (var ,z))))) (lit (pos (app q (app g66.75 (var ,z)) (app g65.74 (var ,z)))))))))))) (and (forall ,(tie x `(forall ,(tie z `(or (lit (pos (app p (var ,x) (var ,z)))) (lit (pos (app q (app g67.76 (var ,z)) (var ,z))))))))) (or (forall ,(tie x `(forall ,(tie y `(lit (neg (app q (var ,x) (var ,y)))))))) (forall ,(tie x `(lit (pos (app r (var ,x) (var ,x))))))))))
            `() `() `() q)))
      `((conj univ savefml conj univ univ conj split
          (savefml conj savefml split
            (savefml conj univ univ split (close)
              (savefml split (univ univ close) (univ close)))
            (savefml conj univ univ split (close)
              (savefml split (univ univ close) (univ close))))
          (savefml conj savefml split (close)
            (savefml conj univ univ split
              (savefml split (univ univ close) (univ close))
              (savefml split (univ univ close) (univ close)))))))
    (pp 37
      `(,(A z ,(E w ,(A x ,(E y (and (=> (p ,x ,z) (p ,y ,w))
                                     (and (p ,y ,z)
                                          (=> (p ,y ,w) ,(E u (q ,u ,w)))))))))
        ,(A x ,(A z (=> (not (p ,x ,z)) ,(E y (q ,y ,z)))))
        (=> ,(E x ,(E y (q ,x ,y))) ,(A x (r ,x ,x))))
      `,(A x ,(E y (r ,x ,y)))))

;; Takes too long
;; (if (switch)
;;     (testit 38
;;       (run 1 (q)
;;         (fresh-nom (x y z w)
;;           (proveo
;;             `(or (and (and (and (lit (pos (app p (sym a)))) (or (lit (neg (app p (app g68.77)))) (and (lit (pos (app p (app g69.78)))) (lit (pos (app r (app g68.77) (app g69.78))))))) (forall ,(tie z `(forall ,(tie w `(or (lit (neg (app p (var ,z)))) (or (lit (neg (app r (app g68.77) (var ,w)))) (lit (neg (app r (var ,w) (var ,z))))))))))) (forall ,(tie x `(and (or (lit (neg (app p (sym a)))) (or (lit (pos (app p (var ,x)))) (and (lit (pos (app p (app g70.79 (var ,x))))) (and (lit (pos (app r (var ,x) (app g71.80 (var ,x))))) (lit (pos (app r (app g71.80 (var ,x)) (app g70.79 (var ,x))))))))) (or (lit (neg (app p (sym a)))) (or (forall ,(tie y `(or (lit (neg (app p (var ,y)))) (lit (neg (app r (var ,x) (var ,y))))))) (and (lit (pos (app p (app g72.81 (var ,x))))) (and (lit (pos (app r (var ,x) (app g73.82 (var ,x))))) (lit (pos (app r (app g73.82 (var ,x)) (app g72.81 (var ,x))))))))))))) (and (forall ,(tie x `(or (or (lit (neg (app p (sym a)))) (and (lit (pos (app p (var ,x)))) (forall ,(tie y `(or (lit (neg (app p (var ,y)))) (lit (neg (app r (var ,x) (var ,y))))))))) (and (lit (pos (app p (app g74.83 (var ,x))))) (and (lit (pos (app r (var ,x) (app g75.84 (var ,x))))) (lit (pos (app r (app g75.84 (var ,x)) (app g74.83 (var ,x)))))))))) (or (and (lit (pos (app p (sym a)))) (and (lit (neg (app p (app g76.85)))) (forall ,(tie z `(forall ,(tie w `(or (lit (neg (app p (var ,z)))) (or (lit (neg (app r (app g76.85) (var ,w)))) (lit (neg (app r (var ,w) (var ,z)))))))))))) (and (lit (pos (app p (sym a)))) (and (and (lit (pos (app p (app g77.86)))) (lit (pos (app r (app g76.85) (app g77.86))))) (forall ,(tie z `(forall ,(tie w `(or (lit (neg (app p (var ,z)))) (or (lit (neg (app r (app g76.85) (var ,w)))) (lit (neg (app r (var ,w) (var ,z)))))))))))))))
;;             `() `() `() q)))
;;       `((split
;;           (conj conj conj savefml split
;;             (savefml univ univ split
;;               (savefml univ conj split (close) (split (close) (conj close)))
;;               (split
;;                 (savefml univ conj split (close)
;;                   (split (close) (conj savefml conj close)))
;;                 (savefml univ conj split (close)
;;                   (split (close) (conj savefml conj savefml close)))))
;;             (conj savefml savefml univ univ split (close)
;;               (split
;;                 (close)
;;                 (savefml univ conj split (close)
;;                   (split
;;                     (savefml
;;                       split
;;                       (close)
;;                       (split
;;                         (univ split (close) (close))
;;                         (conj savefml conj savefml savefml univ univ split (close)
;;                           (split (close) (close)))))
;;                     (conj savefml conj savefml savefml split (close)
;;                       (split
;;                         (univ split (close) (close))
;;                         (conj savefml conj savefml savefml univ univ split (close)
;;                           (split (close) (close))))))))))
;;           (conj
;;             univ
;;             split
;;             (split
;;               (savefml split (conj close) (conj close))
;;               (conj savefml univ split
;;                 (savefml
;;                   split
;;                   (conj savefml conj close)
;;                   (conj savefml conj conj close))
;;                 (savefml
;;                   split
;;                   (conj savefml conj close)
;;                   (conj savefml conj conj savefml close))))
;;             (conj savefml conj savefml savefml split
;;               (conj savefml conj savefml univ univ split (close)
;;                 (split (close) (close)))
;;               (conj savefml conj conj savefml savefml univ univ split (close)
;;                 (split (close) (close))))))))
;;     (pp 38
;;       '()
;;       `(<=> ,(A x (=> (and (p a) (=> (p ,x) ,(E y (and (p ,y) (r ,x ,y)))))
;;                     ,(E z ,(E w (and (p ,z) (and (r ,x ,w) (r ,w ,z)))))))
;;          ,(A x (and
;;                  (or (not (p a)) (or (p ,x) ,(E z ,(E w (and (p ,z)
;;                                                              (and (r ,x ,w)
;;                                                                   (r ,w ,z)))))))
;;                  (or (not (p a))
;;                      (or (not ,(E y (and (p ,y) (r ,x ,y))))
;;                          ,(E z ,(E w (and (p ,z)
;;                                           (and (r ,x ,w)
;;                                                (r ,w ,z))))))))))))

;; Fails
(if (switch)
    (testit 39
      (run 1 (q)
        (fresh-nom (y)
          (proveo 
            `(forall ,(tie y `(or (and (lit (pos (app f (var ,y) (app g0.6)))) (lit (neg (app f (var ,y) (var ,y))))) (and (lit (neg (app f (var ,y) (app g0.6)))) (lit (pos (app f (var ,y) (var ,y))))))))
            `() `() `() q)))
      `((univ split (conj savefml close) (conj savefml close))))

    (pp 39
      '()
      `(not ,(E x ,(A y (<=> (f ,y ,x) (not (f ,y ,y))))))))

(if (switch)
    (testit 40
      (run 1 (q)
        (fresh-nom (x z)
          (proveo
            `(and (forall ,(tie x `(or (and (lit (pos (app f (var ,x) (app g79.88)))) (lit (pos (app f (var ,x) (var ,x))))) (and (lit (neg (app f (var ,x) (app g79.88)))) (lit (neg (app f (var ,x) (var ,x)))))))) (forall ,(tie x `(forall ,(tie z `(or (and (lit (pos (app f (var ,z) (app g80.89 (var ,x))))) (lit (neg (app f (var ,z) (var ,x))))) (and (lit (neg (app f (var ,z) (app g80.89 (var ,x))))) (lit (pos (app f (var ,z) (var ,x)))))))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (conj savefml savefml univ univ split (conj savefml close) (conj close))
          (conj savefml savefml univ univ split (conj close) (conj savefml close)))))
    (pp 40
      '()
      `(=> ,(E y ,(A x (<=> (f ,x ,y) (f ,x ,x))))
         (not ,(A x ,(E y ,(A z (<=> (f ,z ,y) (not (f ,z ,x))))))))))

(if (switch)
    (testit 41
      (run 1 (q)
        (fresh-nom (x z)
          (proveo `(and (forall ,(tie x `(lit (pos (app F (var ,x) (app g0.12)))))) (forall ,(tie z `(forall ,(tie x `(or (and (lit (pos (app F (var ,x) (app g1.13 (var ,z))))) (and (lit (pos (app F (var ,x) (var ,z)))) (lit (neg (app F (var ,x) (var ,x)))))) (and (lit (neg (app F (var ,x) (app g1.13 (var ,z))))) (or (lit (neg (app F (var ,x) (var ,z)))) (lit (pos (app F (var ,x) (var ,x))))))))))))
            `() `() `() q)))
      `((conj univ savefml univ univ split
          (conj savefml conj savefml close)
          (conj savefml split (close) (close)))))

    (pp 41
      `(,(A z ,(E y ,(A x (<=> (F ,x ,y) (and (F ,x ,z) (not (F ,x ,x))))))))
      `(not ,(E z ,(A x (F ,x ,z))))))

(if (switch)
    (testit 42
      (run 1 (q)
        (fresh-nom (x z)
          (proveo
            `(forall ,(tie x `(or (and (lit (pos (app F (var ,x) (app g83.92)))) (forall ,(tie z `(or (lit (neg (app F (var ,x) (var ,z)))) (lit (neg (app F (var ,z) (var ,x)))))))) (and (lit (neg (app F (var ,x) (app g83.92)))) (and (lit (pos (app F (var ,x) (app g84.93 (var ,x))))) (lit (pos (app F (app g84.93 (var ,x)) (var ,x)))))))))
            `() `() `() q)))
      `((univ
          split
          (conj savefml univ split (close) (close))
          (conj savefml conj savefml savefml univ split
            (conj savefml univ split (close) (close)) (conj close)))))
    (pp 42
      '()
      `(not ,(E y ,(A x (<=> (F ,x ,y) (not ,(E z (and (F ,x ,z) (F ,z ,x))))))))))

;; Diverges
;; (if (switch)
;;     (testit 43
;;       (run 1 (q)
;;         (fresh-nom (x y z)
;;           (proveo
;;             `(and (or (and (lit (neg (app Q (app g85.94) (app g86.95)))) (lit (pos (app Q (app g86.95) (app g85.94))))) (and (lit (pos (app Q (app g85.94) (app g86.95)))) (lit (neg (app Q (app g86.95) (app g85.94)))))) (forall ,(tie x `(forall ,(tie y `(or (and (lit (pos (app Q (var ,x) (var ,y)))) (forall ,(tie z `(or (and (lit (pos (app F (var ,z) (var ,x)))) (lit (pos (app F (var ,z) (var ,y))))) (and (lit (neg (app F (var ,z) (var ,x)))) (lit (neg (app F (var ,z) (var ,y))))))))) (and (lit (neg (app Q (var ,x) (var ,y)))) (or (and (lit (neg (app F (app g87.96 (var ,x) (var ,y)) (var ,x)))) (lit (pos (app F (app g87.96 (var ,x) (var ,y)) (var ,y))))) (and (lit (pos (app F (app g87.96 (var ,x) (var ,y)) (var ,x)))) (lit (neg (app F (app g87.96 (var ,x) (var ,y)) (var ,y)))))))))))))
;;             `() `() `() q)))
;;       `((conj
;;           split
;;           (conj savefml savefml univ univ split (conj close)
;;             (conj
;;               savefml
;;               split
;;               (conj savefml savefml univ univ split
;;                 (conj savefml univ split (conj savefml close) (conj close))
;;                 (conj close))
;;               (conj savefml savefml univ univ split
;;                 (conj savefml univ split (conj close) (conj savefml close))
;;                 (conj close))))
;;           (conj savefml savefml univ univ split (conj close)
;;             (conj
;;               savefml
;;               split
;;               (conj savefml savefml univ univ split
;;                 (conj savefml univ split (conj savefml close) (conj close))
;;                 (conj close))
;;               (conj savefml savefml univ univ split
;;                 (conj savefml univ split (conj close) (conj savefml close))
;;                 (conj close)))))))
;;     (pp 43
;;       `(,(A x ,(A y (<=> (Q ,x ,y) ,(A z (<=> (F ,z ,x) (F ,z ,y)))))))
;;       `,(A x ,(A y (<=> (Q ,x ,y) (Q ,y ,x))))))

(if (switch)
    (testit 44
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (forall ,(tie x `(or (lit (neg (app J (var ,x)))) (lit (pos (app F (var ,x))))))) (and (forall ,(tie x `(and (or (lit (neg (app F (var ,x)))) (and (lit (pos (app G (app g2.20 (var ,x))))) (lit (pos (app H (var ,x) (app g2.20 (var ,x))))))) (and (lit (pos (app G (app g3.21 (var ,x))))) (lit (neg (app H (var ,x) (app g3.21 (var ,x))))))))) (and (lit (pos (app J (app g4.22)))) (forall ,(tie y `(or (lit (neg (app G (var ,y)))) (lit (pos (app H (app g4.22) (var ,y))))))))))
            `() `() `() q)))
      `((conj
          univ
          split
          (savefml conj univ conj split (savefml conj savefml savefml conj close)
            (conj savefml savefml conj savefml savefml conj close))
          (savefml conj univ conj split (close)
            (conj savefml savefml conj savefml savefml conj savefml univ split (close)
              (close))))))

    (pp 44
      `(,(A x (and (=> (F ,x) ,(E y (and (G ,y) (H ,x ,y))))
                   ,(E y (and (G ,y) (not (H ,x ,y))))))
        ,(E x (and (J ,x) ,(A y (=> (G ,y) (H ,x ,y))))))
      `,(E x (and (J ,x) (not (F ,x))))))

(if (switch)
    (testit 45
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (forall ,(tie x `(or (lit (neg (app F (var ,x)))) (and (lit (pos (app G (app g91.100 (var ,x))))) (lit (pos (app H (var ,x) (app g91.100 (var ,x))))))))) (and (forall ,(tie x `(and (lit (pos (app F (var ,x)))) (forall ,(tie y `(or (or (lit (neg (app G (var ,y)))) (and (lit (pos (app H (var ,x) (var ,y)))) (lit (neg (app J (var ,x) (var ,y)))))) (forall ,(tie y `(and (lit (pos (app G (var ,y)))) (or (lit (neg (app H (var ,x) (var ,y)))) (lit (pos (app K (var ,y)))))))))))))) (and (forall ,(tie y `(or (lit (neg (app L (var ,y)))) (lit (neg (app K (var ,y))))))) (and (and (lit (pos (app F (app g92.101)))) (forall ,(tie y `(or (lit (neg (app H (app g92.101) (var ,y)))) (lit (pos (app L (var ,y)))))))) (forall ,(tie y `(and (lit (pos (app G (var ,y)))) (or (lit (neg (app H (app g92.101) (var ,y)))) (lit (pos (app J (app g92.101) (var ,y))))))))))))
            `() `() `() q)))
      `((conj
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
                (savefml conj conj savefml univ split (close) (close)) (close)))))))

    (pp 45
      `(,(A x (and (F ,x) ,(A y (=> (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))
                                  ,(A y (and (G ,y) (=> (H ,x ,y) (K ,y))))))))
        (not ,(E y (and (L ,y) (K ,y))))
        ,(E x (and (and (F ,x) ,(A y (=> (H ,x ,y) (L ,y))))
                   ,(A y (and (G ,y) (=> (H ,x ,y) (J ,x ,y)))))))
      `,(E x (and (F ,x) (not ,(E y (and (G ,y) (H ,x ,y))))))))

(if (switch)
    (testit 46
      (run 1 (q)
        (fresh-nom (x y)
          (proveo
            `(and (and (lit (pos (app F (app g24.33)))) (lit (neg (app G (app g24.33))))) (and (forall ,(tie x `(or (or (lit (neg (app F (var ,x)))) (and (and (lit (pos (app F (app g25.34 (var ,x))))) (lit (pos (app H (app g25.34 (var ,x)) (var ,x))))) (lit (neg (app G (app g25.34 (var ,x))))))) (lit (pos (app G (var ,x))))))) (and (or (forall ,(tie x `(or (lit (neg (app F (var ,x)))) (lit (pos (app G (var ,x))))))) (and (lit (pos (app F (app g26.35)))) (and (lit (neg (app G (app g26.35)))) (forall ,(tie y `(or (or (lit (neg (app F (var ,y)))) (lit (pos (app G (var ,y))))) (lit (pos (app J (app g26.35) (var ,y)))))))))) (forall ,(tie x `(forall ,(tie y `(or (or (lit (neg (app F (var ,x)))) (or (lit (neg (app F (var ,y)))) (lit (neg (app H (var ,x) (var ,y)))))) (lit (neg (app J (var ,y) (var ,x))))))))))))
            `() `() `() q)))
      `((conj conj savefml savefml conj univ split
          (split
            (savefml conj split (univ split (close) (close)) (conj close))
            (conj conj savefml savefml savefml conj split (univ split (close) (close))
              (conj savefml conj savefml univ split (split (close) (close))
                (savefml univ univ split (split (close) (split (close) (close)))
                  (close)))))
          (savefml conj split (univ split (close) (close)) (conj savefml conj close)))))

    (pp 46
      `(,(A x (=> (and (F ,x) ,(A y (=> (and (F ,y) (H ,y ,x))
                                      (G ,y))))
                (G ,x)))
        (=> ,(E x (and (F ,x) (not (G ,x))))
          ,(E x (and (F ,x) (and (not (G ,x))
                                 ,(A y (=> (and (F ,y) (not (G ,y))) (J ,x ,y)))))))
        ,(A x ,(A y (=> (and (F ,x) (and (F ,y) (H ,x ,y))) (not (J ,y ,x))))))
      `,(A x (=> (F ,x) (G ,x)))))

(printf "all done!\n")

