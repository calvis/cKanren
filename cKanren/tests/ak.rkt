#lang racket

;;; And now the tests from the old alphamk.scm

(require
 (rename-in "../unstable/ak.rkt" [nominal-== ==])
 "../tester.rkt"
 "nominal/nnf.rkt" 
 "nominal/alphaleantap.rkt"
 "../src/operators.rkt"
 (only-in "../ck.rkt" run run* fresh conde))

(provide test-ak test-ak-long)

(define (test-ak)
  (test (run 1 (q) (== 3 3)) '(_.0))

  (test (run 1 (q) (== 5 6)) '())

  (test (run 1 (q) (== q 3)) '(3))

  (test (run 1 (q) (fresh (x) (== x q))) '(_.0))

  (test (run 1 (q) (fresh (x y z) (== x z) (== 3 y))) '(_.0))

  (test (run 1 (q) (fresh (x y) (== x q) (== 3 y))) '(_.0))

  (test (run 1 (y)
          (fresh (x z) 
            (== x z)
            (== 3 y)))
        '(3))

  (test
   (run 1 (q)
     (fresh (x z)
       (== x z)
       (== 3 z)
       (== q x)))
   '(3))

  (test (run 1 (y)
          (fresh (x y)
            (== 4 x)
            (== x y))
          (== 3 y))
        '(3))

  (test (run 1 (x) (== 4 3))
        '())
  
  (test
   (run 2 (q)
     (fresh (x y z)
       (conde
        ((== `(,x ,y ,z ,x) q))
        ((== `(,z ,y ,x ,z) q)))))
   '((_.0 _.1 _.2 _.0)
     (_.0 _.1 _.2 _.0)))
  
  (test
   (run 5 (q)
     (let loop ()
       (conde
        ((== #f q))
        ((== #t q))
        ((loop)))))
   '(#f #t #f #t #f))
  
  (define anyo 
    (lambda (g)
      (conde
       (g)
       ((anyo g)))))

  (test
   (run 5 (q)
     (conde
      ((anyo (== #f q)))
      ((== #t q))))
   '(#t #f #f #f #f))
  
  (test
   (run 10 (q)
     (anyo 
      (conde
       ((== 1 q))
       ((== 2 q))
       ((== 3 q)))))
   '(1 2 3 1 2 3 1 2 3 1))
  
  (test
   (run 3 (q)
     (let ((nevero (anyo (== #f #t))))
       (conde
        ((== 1 q))
        (nevero)
        ((conde
          ((== 2 q))
          (nevero)
          ((== 3 q)))))))
   '(1 2 3))
  
  (test
   (run* (q) (fresh-nom (a) (== a a)))
   '(_.0))
  
  (test
   (run* (q) (fresh-nom (a) (== a 5)))
   '())
  
  (test
   (run* (q) (fresh-nom (a b) (== a b)))
   '())

  (test
   (run* (q) (fresh-nom (a b) (== b q)))
   '(a.0))

  (test
   (run* (q)
     (fresh (x y z)
       (fresh-nom (a)
                  (== x a)
                  (fresh-nom (a b)
                             (== y a)
                             (== `(,x ,y ,z ,a ,b) q)))))
   '((a.0 a.1 _.2 a.1 a.3)))

  (test
   (run* (q)
     (fresh-nom (a b)
                (== (tie a `(foo ,a 3 ,b)) q)))
   '((tie a.0 (foo a.0 3 a.1))))
  
  (test
   (run* (q) (fresh-nom (a b) (== `(foo ,a ,a) `(foo ,b ,b))))
   '())
  
  (test
   (run* (q) (fresh-nom (a b) (== (tie a a) (tie b b))))
   '(_.0))
  
  (test
   (run* (q) (fresh-nom (a b) (== (tie a q) (tie b b))))
   '(a.0))
  
  (test
   (run* (q)
     (fresh (t u)
       (fresh-nom (a b c d)
                  (== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
                  (== `(lam ,(tie c `(lam ,(tie d `(var ,c))))) u)
                  (== t u))))
   '(_.0))
  
  (test
   (run* (q)
     (fresh (t u)
       (fresh-nom (a b c d)
                  (== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
                  (== `(lam ,(tie c `(lam ,(tie d `(var ,d))))) u)
                  (== t u))))
   '())
  
  (test
   (run* (q) (fresh-nom (a) (hash a a)))
   '())
  
  (test
   (run* (q) (fresh-nom (a) (hash a 5)))
   '(_.0))

  (test
   (run* (q) (fresh-nom (a) (hash a (tie a a))))
   '(_.0))
  
  (test
   (run* (q) (fresh-nom (a b) (hash a (tie b a))))
   '())
  
  (test-highlight
   (run* (k)
     (fresh (t)
       (fresh-nom (a)
         (hash a k)
         (== `(5 ,(tie a a) ,t) k)
         prt)))
   '(((5 (tie a.0 a.0) _.1) : (alpha (hash (a.0 _.1))))))

  (test 32
          (run* (k)
            (fresh (t)
              (fresh-nom (a)
                         (hash a k) 
                         (== `(5 ,(tie a a) ,t) k)
                         (== `(foo ,a 7) t))))
          '())

  (test 33
          (run* (k)
            (fresh (t)
              (fresh-nom (a b)
                         (== (tie a (tie b t)) k) 
                         (hash a t)
                         (== `((,a ,b) ,b) t))))
          '())

  (test 34
          (run* (k)
            (fresh (t)
              (fresh-nom (a b)
                         (== (tie a (tie b t)) k) 
                         (hash a t)
                         (== `(,b ,(tie a `(,a (,b ,b)))) t))))
          '((tie a.0 (tie a.1 (a.1 (tie a.0 (a.0 (a.1 a.1))))))))

  (test 35
          (run* (q)
            (fresh (k1 k2 t u)
              (fresh-nom (a b c d)
                         (== (tie a (tie b t)) k1)
                         (hash a t)
                         (== (tie c (tie d u)) k2)
                         (hash c u)
                         (== k1 k2)
                         (== `(,k1 ,k2) q))))
          
          '((((tie a.0 (tie a.1 (sus _.2 ((a.1 . a.3) (a.0 . a.4)))))
              (tie a.4 (tie a.3 _.2)))
             :
             (alpha
              (hash (a.0 _.2)) 
              (hash (a.1 _.2)) 
              (hash (a.4 _.2))))))

  (test 36
          (run* (q)
            (fresh (k1 k2 t u)
              (fresh-nom (a b c d)
                         (== (tie a (tie b t)) k1) 
                         (hash a t)
                         (== `(,b ,b) t)
                         (== (tie c (tie d u)) k2)
                         (hash c u)
                         (== `(,d ,d) u)
                         (== k1 k2)
                         (== `(,k1 ,k2) q))))
          '(((tie a.0 (tie a.1 (a.1 a.1)))
             (tie a.2 (tie a.3 (a.3 a.3))))))

  (test 37
          (run* (q)
            (fresh-nom (a b)
                       (fresh (x y)
                         (== (tie a (tie a x)) (tie a (tie b y)))
                         (== `(,x ,y) q))))
          '(((_.0 (sus _.0 ((a.1 . a.2))))
             :
             (alpha (hash (a.2 _.0))))))

  (test 38.0
          (run* (q)
            (fresh-nom (a b)
                       (== (tie a (tie b `(,q ,b))) (tie b (tie a `(,a ,q))))))
          '())

  (test 38.1
          (run* (q)
            (fresh-nom (a b)
                       (fresh (x y)
                         (conde
                          ((== (tie a (tie b `(,x ,b))) (tie b (tie a `(,a ,x)))))
                          ((== (tie a (tie b `(,y ,b))) (tie b (tie a `(,a ,x)))))
                          ((== (tie a (tie b `(,b ,y))) (tie b (tie a `(,a ,x)))))
                          ((== (tie a (tie b `(,b ,y))) (tie a (tie a `(,a ,x))))))
                         (== `(,x ,y) q))))
          '(((sus _.0 ((a.1 . a.2))) _.0)
            (a.0 a.1)
            (((sus _.0 ((a.1 . a.2))) _.0) : (alpha (hash (a.2 _.0))))))

  (define substo  
    (lambda (e new a out)
      (conde
       ((== `(var ,a) e) (== new out))
       ((fresh (y)
          (== `(var ,y) e)
          (== `(var ,y) out)
          (hash a y)))
       ((fresh (rator ratorres rand randres)
          (== `(app ,rator ,rand) e)
          (== `(app ,ratorres ,randres) out)
          (substo rator new a ratorres)
          (substo rand new a randres)))
       ((fresh (body bodyres)
          (fresh-nom (c)
                     (== `(lam ,(tie c body)) e)
                     (== `(lam ,(tie c bodyres)) out)
                     (hash c a)
                     (hash c new)
                     (substo body new a bodyres)))))))

  (test 39.0
          (run* (x)
            (fresh-nom (a b)
                       (substo `(lam ,(tie a `(var ,b))) `(var ,a) b x)))
          '((lam (tie a.0 (var a.1)))))

  (test 39.1
          (run* (q)
            (fresh-nom (a)
                       (substo
                        `(lam ,(tie a `(var ,a))) 5 a q)))
          '((lam (tie a.0 (var a.0)))))

  (test 40
          (run* (q)
            (fresh-nom (a b)
                       (substo
                        `(lam ,(tie a `(app (var ,a) (var ,b)))) b a q)))
          '((lam (tie a.0 (app (var a.0) (var a.1))))))


  (define typo
    (lambda (g e te)
      (conde
       ((fresh (x)
          (== `(var ,x) e)
          (lookupo x te g)))
       ((fresh (rator trator rand trand)
          (== `(app ,rator ,rand) e)
          (== `(-> ,trand ,te) trator)
          (typo g rator trator)
          (typo g rand trand)))
       ((fresh (e^ te^ trand g^)
          (fresh-nom (b)
                     (== `(lam ,(tie b e^)) e)
                     (== `(-> ,trand ,te^) te)
                     (hash b g)
                     (== `((,b . ,trand) . ,g) g^)
                     (typo g^ e^ te^))))
       ((fresh (rator t-val)
          (== `(C ,rator) e)
          (typo g rator `(-> (-> ,te ,t-val) ,t-val)))))))

  (define !-c
    (lambda (gamma exp type)
      (fresh (m a b)
        (== `(c ,m) exp)
        (== a type)
        (typo gamma m `(-> (-> ,a ,b) ,b)))))

  (define lookupo
    (lambda (x tx g)
      (fresh (a d)
        (== `(,a . ,d) g)
        (conde
         ((== `(,x . ,tx) a))
         ((fresh (x^ tx^)
            (== `(,x^ . ,tx^) a)
            (hash x x^)
            (lookupo x tx d)))))))

  (test 41
          (run* (q)
            (fresh-nom (c d)
                       (typo '() `(lam ,(tie c `(lam ,(tie d `(var ,c))))) q)))
          '((-> _.0 (-> _.1 _.0))))

  (test 42
          (run* (q)
            (fresh-nom (c d)
                       (typo '() `(lam ,(tie c `(lam ,(tie d `(var ,c))))) q)))
          '((-> _.0 (-> _.1 _.0))))

  ;; WEB 5 Feb 2012
  ;; diverges?
  ;; not sure what is up with this one
  ;; (test 42.1
  ;;   (run* (q)
  ;;     (fresh-nom (c)
  ;;       (typo '() `(lam ,(tie c `(app (var ,c) (var ,c)))) q)))
  ;;   '())

  (test 43
          (run 5 (q) (typo '() q '(-> int int)))
          '((lam (tie a.0 (var a.0)))
            (C (lam (tie a.0 (var a.0))))
            (app (lam (tie a.0 (var a.0))) (lam (tie a.1 (var a.1))))
            (lam (tie a.0 (C (lam (tie a.1 (var a.1))))))
            (lam (tie a.0 (app (lam (tie a.1 (var a.1))) (var a.0))))))

  (test 44
          (run* (q)
            (fresh (x y z)
              (fresh-nom (a)      
                         (hash a x)
                         (== `(,y ,z) x)
                         (== `(,x ,a) q))))
          '((((_.0 _.1) a.2) : (alpha (hash (a.2 _.0)) (hash (a.2 _.1))))))

  )

(define (test-ak-long)
  (test-ak)

  (define-syntax pp
    (syntax-rules ()
      ((_ n axioms theorem)
       (begin
         (printf "Pelletier Problem ~s\n" n)
         (let ((pr (do-prove-th axioms theorem))) pr)))))

  (define-syntax testit
    (syntax-rules ()
      ((_ num exp val)
       (test num exp val))))

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

  (testit 18
          (run 1 (q)
            (fresh-nom (y)
                       (proveo
                        `(forall ,(tie y
                                       `(and (lit (pos (app f (var ,y))))
                                             (lit (neg (app f (app g0.6 (var ,y))))))))
                        `() `() `() q)))
          `((univ conj savefml savefml univ conj close)))

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

  (testit 35
          (run 1 (q)
            (fresh-nom (x y)
                       (proveo
                        `(forall ,(tie x `(forall ,(tie y `(and (lit (pos (app p (var ,x) (var ,y)))) (lit (neg (app p (app g58.67) (app g59.68)))))))))
                        `() `() `() q)))
          `((univ univ conj savefml close)))

  (testit 36
          (run 1 (q)
            (fresh-nom (x y z)
                       (proveo
                        `(and (forall ,(tie y `(lit (neg (app h (app g60.69) (var ,y)))))) (and (forall ,(tie x `(lit (pos (app f (var ,x) (app g61.70 (var ,x))))))) (and (forall ,(tie x `(lit (pos (app g (var ,x) (app g62.71 (var ,x))))))) (forall ,(tie x `(forall ,(tie y `(or (and (lit (neg (app f (var ,x) (var ,y)))) (lit (neg (app g (var ,x) (var ,y))))) (forall ,(tie z `(or (and (lit (neg (app f (var ,y) (var ,z)))) (lit (neg (app g (var ,y) (var ,z))))) (lit (pos (app h (var ,x) (var ,z)))))))))))))))
                        `() `() `() q)))
          `((conj univ savefml conj univ savefml conj univ savefml univ univ split
                  (conj close) (univ split (conj savefml close) (close)))))

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
  (testit 39
          (run 1 (q)
            (fresh-nom (y)
                       (proveo 
                        `(forall ,(tie y `(or (and (lit (pos (app f (var ,y) (app g0.6)))) (lit (neg (app f (var ,y) (var ,y))))) (and (lit (neg (app f (var ,y) (app g0.6)))) (lit (pos (app f (var ,y) (var ,y))))))))
                        `() `() `() q)))
          `((univ split (conj savefml close) (conj savefml close))))

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

  (testit 41
          (run 1 (q)
            (fresh-nom (x z)
                       (proveo `(and (forall ,(tie x `(lit (pos (app F (var ,x) (app g0.12)))))) (forall ,(tie z `(forall ,(tie x `(or (and (lit (pos (app F (var ,x) (app g1.13 (var ,z))))) (and (lit (pos (app F (var ,x) (var ,z)))) (lit (neg (app F (var ,x) (var ,x)))))) (and (lit (neg (app F (var ,x) (app g1.13 (var ,z))))) (or (lit (neg (app F (var ,x) (var ,z)))) (lit (pos (app F (var ,x) (var ,x))))))))))))
                               `() `() `() q)))
          `((conj univ savefml univ univ split
                  (conj savefml conj savefml close)
                  (conj savefml split (close) (close)))))

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

  (printf "all done!\n")

)

(module+ main
  (test-ak-long))
