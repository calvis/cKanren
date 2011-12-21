(load "ck.scm")
(load "fd.scm")
(load "neq.scm")

(define n-queenso
  (lambda (q n)
    (let loop ((i n) (l '()))
      (cond
        ((zero? i)
         (fresh ()
           (== q l)
           (distinctfd l)
           (diagonalso n l)))
        (else
         (fresh (x)
           (infd x (range 1 n))
           (loop (sub1 i) (cons x l))))))))

(define diagonalso
  (lambda (n l)
    (let loop ((r l) (s (cdr l)) (i 0) (j 1))
      (cond
        ((or (null? r) (null? (cdr r))) succeed)
        ((null? s) (loop (cdr r) (cddr r) (+ i 1) (+ i 2)))
        (else
          (let ((qi (car r)) (qj (car s)))
            (fresh ()
              (diago qi qj (- j i) (range 0 (* 2 n)))
              (loop r (cdr s) i (+ j 1)))))))))

(define diago
  (lambda (qi qj d rng)
    (fresh (si sj)
      (infd si sj rng)
      (=/=fd qi sj)
      (plusfd qi d si)
      (=/=fd qj si)
      (plusfd qj d sj))))

(define distincto
  (lambda (l)
    (conde
      ((== l '()))
      ((fresh (a) (== l `(,a))))
      ((fresh (a ad dd)
         (== l `(,a ,ad . ,dd))
         (=/= a ad)
         (distincto `(,a . ,dd))
         (distincto `(,ad . ,dd)))))))

(test-check "Distinct Queens 1"
  (run* (q)
    (fresh (x)
      (n-queenso x 8)
      (distincto x)))
  '(_.0))

(test-check "Distinct Queens 2"
  (let ((answers (run* (q) (n-queenso q 4))))
    (run* (q) (distincto answers)))
  '(_.0))

(test-check "infd/Distinct 1"
  (run* (q) (infd q '(2 3 4)) (distincto `(a 3 ,q)))
  '(2 4))

