(load "tester.scm")
(load "ck.scm")
(load "tree-unify.scm")
(load "neq.scm")

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

(test-check "=/=--1"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== `(,x ,y) q)))
  '(((_.0 _.1) : (=/= ((_.0 . 2) (_.1 . 1))))))

;;; #!eof (when tracing)

(test-check "=/=-0"
  (run* (q)
    (fresh (x y z)
      (=/= `(,x 2 ,z)  `(1 ,z 3))
      (=/= `(,x 6 ,z)  `(4 ,z 6))
      (=/= `(,x ,y ,z)  `(7 ,z 9))
      (== x z)
      (== q `(,x ,y ,z))))
  '((_.0 _.1 _.0)))

(test-check "=/=-1"
  (run* (q)
    (=/= 3 q)
    (== q 3))
  '())

(test-check "=/=-2"
  (run* (q)
    (== q 3)
    (=/= 3 q))
  '())

(test-check "=/=-3"
  (run* (q)
    (fresh (x y)
      (=/= x y)
      (== x y)))
  '())

(test-check "=/=-4"
  (run* (q)
    (fresh (x y)
      (== x y)
      (=/= x y)))
  '())

(test-check "=/=-5"
  (run* (q)
    (fresh (x y)
      (=/= x y)
      (== 3 x)
      (== 3 y)))
  '())

(test-check "=/=-6"
  (run* (q)
    (fresh (x y)
      (== 3 x)
      (=/= x y)
      (== 3 y)))
  '())

(test-check "=/=-7"
  (run* (q)
    (fresh (x y)
      (== 3 x)
      (== 3 y)
      (=/= x y)))
  '())

(test-check "=/=-8"
  (run* (q)
    (fresh (x y)
      (== 3 x)
      (== 3 y)
      (=/= y x)))
  '())

(test-check "=/=-9"
  (run* (q)
    (fresh (x y z)
      (== x y)
      (== y z)
      (=/= x 4)
      (== z (+ 2 2))))
  '())

(test-check "=/=-10"
  (run* (q)
    (fresh (x y z)
      (== x y)
      (== y z)
      (== z (+ 2 2))
      (=/= x 4)))
  '())

(test-check "=/=-11"
  (run* (q)
    (fresh (x y z)
      (=/= x 4)
      (== y z)
      (== x y)
      (== z (+ 2 2))))
  '())

(test-check "=/=-12"
  (run* (q)
    (fresh (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '(_.0))

(test-check "=/=-13"
  (run* (q)
    (fresh (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (== z 1)
      (== `(,x ,y) q)))
  '())

(test-check "=/=-14"
  (run* (q)
    (fresh (x y z)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (== z 0)))
  '(_.0))

(test-check "=/=-15"
  (run* (q)
    (fresh (x y z)
      (== z 0)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '(_.0))

(test-check "=/=-16"
  (run* (q)
    (fresh (x y z)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (=/= x y)))
  '(_.0))

(test-check "=/=-17"
  (run* (q)
    (fresh (x y z)
      (== z 1)
      (=/= x y)
      (== x `(0 ,z 1))
      (== y `(0 1 1))))
  '())

(test-check "=/=-18"
  (run* (q)
    (fresh (x y z)
      (== z 1)
      (== x `(0 ,z 1))
      (== y `(0 1 1))
      (=/= x y)))
  '())

(test-check "=/=-19"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)))
  '(_.0))

(test-check "=/=-20"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== y 1)))
  '(_.0))

(test-check "=/=-21"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 1)))
  '())

(test-check "=/=-22"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== `(,x ,y) q)))
  '(((_.0 _.1) : (=/= ((_.0 . 2) (_.1 . 1))))))

(test-check "=/=-23"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== `(,x ,y) q)))
  '(((2 _.0) : (=/= ((_.0 . 1))))))

(test-check "=/=-24"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 9)
      (== `(,x ,y) q)))
  '((2 9)))

(test-check "=/=-25"
  (run* (q)
    (fresh (x y)
      (=/= `(,x 1) `(2 ,y))
      (== x 2)
      (== y 1)
      (== `(,x ,y) q)))
  '())

(test-check "=/=-26"
  (run* (q)
    (fresh (a x z)
      (=/= a `(,x 1))
      (== a `(,z 1))
      (== x z)))
  '())

(test-check "=/=-27"
  (run* (q)
    (fresh (a x z)
      (=/= a `(,x 1))
      (== a `(,z 1))
      (== x 5)
      (== `(,x ,z) q)))
  '(((5 _.0) : (=/= ((_.0 . 5))))))

(test-check "=/=-28"
  (run* (q)
    (=/= 3 4))
  '(_.0))

(test-check "=/=-29"
  (run* (q)
    (=/= 3 3))
  '())

(test-check "=/=-30"
  (run* (q)
    (fresh (a)
      (=/= a 3)
      (== 3 a)))
  '())

(test-check "=/=-31"
  (run* (q)
    (fresh (a)
      (== 3 a)
      (=/= a 3)))
  '())

(test-check "=/=-32"
  (run* (q)
    (fresh (a)
      (== 3 a)
      (=/= a 4)))
  '(_.0))


(test-check "=/=-33"
  (run* (q)
    (=/= 4 q)
    (=/= 3 q))
  '((_.0 : (=/= ((_.0 . 3)) ((_.0 . 4))))))


(test-check "=/=-34"
  (run* (q) (=/= q 5) (=/= q 5))
  '((_.0 : (=/= ((_.0 . 5))))))


(test-check "=/=-35"
  (let ((foo (lambda (x)
               (fresh (a)
                 (=/= x a)))))
    (run* (q) (fresh (a) (foo a))))
  '(_.0))

(test-check "=/=-36"
  (let ((foo (lambda (x)
               (fresh (a)
                 (=/= x a)))))
    (run* (q) (fresh (b) (foo b))))
  '(_.0))


(test-check "=/=-37"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= x y)))
  '(((_.0 _.1) : (=/= ((_.0 . _.1))))))


(test-check "=/=-38"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= y x)))
  '(((_.0 _.1) : (=/= ((_.1 . _.0))))))

(test-check "=/=-39"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= x y)
      (=/= y x)))
  '(((_.0 _.1) : (=/= ((_.0 . _.1)))))) 

(test-check "=/=-40"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= x y)
      (=/= x y)))
  '(((_.0 _.1) : (=/= ((_.0 . _.1))))))

(test-check "=/=-41"
  (run* (q) (=/= q 5) (=/= 5 q))
  '((_.0 : (=/= ((_.0 . 5))))))

(test-check "=/=-42"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= `(,x ,y) `(5 6))
      (=/= x 5)))
  '(((_.0 _.1) : (=/= ((_.0 . 5))))))

(test-check "=/=-43"
  (run* (q)
    (fresh (x y)
      (== `(,x ,y) q)
      (=/= x 5)
      (=/= `(,x ,y) `(5 6))))
  '(((_.0 _.1) : (=/= ((_.0 . 5))))))

(test-check "=/=-44"
  (run* (q)
    (fresh (x y)
      (=/= x 5)
      (=/= `(,x ,y) `(5 6))
      (== `(,x ,y) q)))
  '(((_.0 _.1) : (=/= ((_.0 . 5))))))

(test-check "=/=-45"
  (run* (q)
    (fresh (x y)
      (=/= 5 x)
      (=/= `(,x ,y) '(5 6))
      (== `(,x ,y) q)))
  '(((_.0 _.1) : (=/= ((_.0 . 5))))))

(test-check "=/=-46"
  (run* (q)
    (fresh (x y)
      (=/= 5 x)
      (=/= `( ,y ,x) `(6 5))
      (== `(,x ,y) q)))
  '(((_.0 _.1) : (=/= ((_.0 . 5))))))

(test-check "=/=-47"
  (run* (x)
    (fresh (y z)
      (=/= x `(,y 2))
      (== x `(,z 2))))
  '((_.0 2)))

(test-check "=/=-48"
  (run* (x)
    (fresh (y z)
      (=/= x `(,y 2))
      (== x `((,z) 2))))
  '(((_.0) 2)))

(test-check "=/=-49"
  (run* (x)
    (fresh (y z)
      (=/= x `((,y) 2))
      (== x `(,z 2))))
  '((_.0 2)))

(test-check "=/=-50"
  (run* (q)
    (distincto `(2 3 ,q)))
  '((_.0 : (=/= ((_.0 . 2)) ((_.0 . 3))))))

(define rembero
  (lambda (x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((fresh (a d res)
         (== `(,a . ,d) ls)
         (rembero x d res)
         (conde
           ((== a x) (== out res))
           ((== `(,a . ,res) out))))))))

(test-check "=/=-51"
  (run* (q) (rembero 'a '(a b a c) q))
  '((b c) (b a c) (a b c) (a b a c)))

(test-check "=/=-52"
  (run* (q) (rembero 'a '(a b c) '(a b c)))
  '(_.0))

(define rembero
  (lambda (x ls out)
    (conde
      ((== '() ls) (== '() out))
      ((fresh (a d res)
         (== `(,a . ,d) ls)
         (rembero x d res)
         (conde
           ((== a x) (== out res))
           ((=/= a x) (== `(,a . ,res) out))))))))

(test-check "=/=-53"
  (run* (q) (rembero 'a '(a b a c) q))
  '((b c)))

(test-check "=/=-54"
  (run* (q) (rembero 'a '(a b c) '(a b c)))
  '())