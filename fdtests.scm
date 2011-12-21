(load "tester.scm")
(load "ck.scm")
(load "fd.scm")
(load "tree-unify.scm")

;; (test-check "-1"
;;   (run* (q)
;;     (fresh (w x y z)
;;       (infd w z (range 1 5))
;;       (distinctfd q)
;;       (== q `(,x ,y ,z))
;;       (== `(,x 2) `(1 ,y))
;;       (plusfd x y w)
;;       (plusfd w y z)))
;;   '((1 2 5)))

;; ;;; #!eof  (when tracing, uncomment)


;; (test-check "0"
;;   (run* (q)
;;     (fresh (a b c)
;;       (distinctfd q)
;;       (== q `(,a ,b ,c))
;;       (infd a b c '(1 2 3))
;;       (== a 1)
;;       (== b 2)
;;       (<=fd c 5)))
;;  '((1 2 3)))

(test-check "1^^"
  (run* (x)
    (infd x '(1 2)))
  '(1 2))

(test-check "1^"
  (run* (x)
    (infd x '(1 2))
    (=/=fd x 1))
  `(2))

(test-check "1"
  (run* (q)
    (fresh (x)
      (infd x q '(1 2))
      (=/=fd x 1)
      (=fd x q)))
  `(2))

(test-check "2"
  (run* (q)
    (fresh (x y z)
      (infd x '(1 2 3))
      (infd y '(3 4 5))
      (=fd x y)
      (infd z '(1 3 5 7 8))
      (infd z '(5 6))
      (=fd z 5)
      (== q `(,x ,y ,z))))
  `((3 3 5)))

(test-check "3"
  (run* (q)
    (fresh (x y z)
      (infd x '(1 2 3))
      (infd y '(3 4 5))
      (=fd x y)
      (infd z '(1 3 5 7 8))
      (infd z '(5 6))
      (=fd z x)
      (== q `(,x ,y ,z))))
  '())

(test-check "4"
  (run* (q)
    (fresh (x y z) 
      (infd x '(1 2))
      (infd y '(2 3))
      (infd z q '(2 4))
      (=fd x y)
      (=/=fd x z)
      (=fd q z)))
  `(4))

(test-check "4.1"
  (run* (q)
    (fresh (x y z) 
      (=fd x y)
      (infd y '(2 3))
      (=/=fd x z)
      (infd z q '(2 4))
      (=fd q z)
      (infd x '(1 2))))
  `(4))

(test-check "5"
  (run* (q)
    (fresh (x y)
      (infd x '(1 2 3))
      (infd y '(0 1 2 3 4))
      (<fd x y)
      (=/=fd x 1)
      (=fd y 3)
      (== q `(,x ,y))))
  `((2 3)))

(test-check "6"
  (run* (q)
    (fresh (x y)
      (infd x '(1 2))
      (infd y '(2 3))
      (=fd x y)
      (== q `(,x ,y))))
  `((2 2)))

(test-check "7"
  (run* (q)
    (fresh (x y z)
      (infd x y z '(1 2))
      (=/=fd x y)
      (=/=fd x z)
      (=/=fd y z))
    (infd q '(5)))
  `())

(test-check "8"
  (run* (q)
    (fresh (x) (infd x '(1 2)))
    (infd q '(5)))
  `(5))

(test-check "9"
  (run* (q)
    (== q #t))
  `(#t))

(test-check "10"
  (run* (q)
    (infd q '(1 2))
    (== q #t))
  `())

(test-check "11"
  (run* (q)
    (== q #t)
    (infd q '(1 2)))
  `())

(test-check "12"
  (run* (q)
    (fresh (x)
      (<=fd x 5)
      (infd x q (range 0 10))
      (=fd q x)))
  `(0 1 2 3 4 5))

(test-check "13"
  (run* (q)
    (fresh (x y z)
      (infd x y z q (range 0 9))
      (=/=fd x y)
      (=/=fd y z)
      (=/=fd x z)
      (=fd x 2)
      (=fd q 3)
      (plusfd y 3 z)))
  `(3))

(test-check "14"
  (run* (q)
    (fresh (x y z)
      (infd x y z (range 0 2))
      (distinctfd `(,x ,y ,z))
      (== q `(,x ,y ,z))))
  `((0 1 2) (0 2 1) (1 0 2) (2 0 1) (1 2 0) (2 1 0)))

(test-check "15"
  (run* (q)
    (fresh (a b c x)
      (infd a b c (range 1 3))
      (distinctfd `(,a ,b ,c))
      (=/=fd c x)
      (<=fd b 2)
      (== x 3)
      (== q `(,a ,b ,c))))
  '((3 1 2) (3 2 1)))

(define add-digitso
  (lambda (augend addend carry-in carry digit)
    (fresh (partial-sum sum)
      (infd partial-sum (range 0 18))
      (infd sum (range 0 19))
      (plusfd augend addend partial-sum)
      (plusfd partial-sum carry-in sum)
      (conde
        ((<fd 9 sum) (=fd carry 1) (plusfd digit 10 sum))
        ((<=fd sum 9) (=fd carry 0) (=fd digit sum))))))

;;; 34 + 89

(test-check "long-addition-step"
  (run* (q)
    (fresh (digit1 digit2 carry0 carry1)
      (infd carry0 carry1 (range 0 1))
      (infd digit1 digit2 (range 0 9))
      (add-digitso 4 9 0 carry0 digit1)
      (add-digitso 3 8 carry0 carry1 digit2)
      (== q `(,carry1 ,digit2 ,digit1))))
  '((1 2 3)))

;;; ((1 2 3))
  
(define send-more-moneyo
  (lambda (letters)
    (fresh (s e n d m o r y carry0 carry1 carry2)
      (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
      (distinctfd letters)
      (infd s m (range 1 9))
      (infd e n d o r y (range 0 9))
      (infd carry0 carry1 carry2 (range 0 1))      
      (add-digitso d e 0 carry0 y)
      (add-digitso n r carry0 carry1 e)
      (add-digitso e o carry1 carry2 n)
      (add-digitso s m carry2 m o))))

(define send-more-moneyo
  (lambda (letters)
    (fresh (s e n d m o r y carry0 carry1 carry2)
      (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
      (distinctfd letters)
      (infd s m (range 1 9))
      (infd e n d o r y (range 0 9))
      (infd carry0 carry1 carry2 (range 0 1))      
      (add-digitso s m carry2 m o)
      (add-digitso e o carry1 carry2 n)
      (add-digitso n r carry0 carry1 e)
      (add-digitso d e 0 carry0 y))))

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
    (fresh (qi+d qj+d)
      (infd qi+d qj+d rng)
      (plusfd qi d qi+d)
      (=/=fd qi+d qj)
      (plusfd qj d qj+d)
      (=/=fd qj+d qi))))

(define n-queenso
  (lambda (q* n)
    (let loop ((i n) (l '()))
      (cond
        ((zero? i)
         (fresh ()
           (distinctfd l)
           (diagonalso n l)
           (== q* l)))
        (else (fresh (x)
                (infd x (range 1 n))
                (loop (sub1 i) (cons x l))))))))

(printf "~s\n" (time (run* (q) (send-more-moneyo q))))
(printf "~s\n" (time (run 1 (q) (n-queenso q 8))))
(printf "~s\n" (time (length (run* (q) (n-queenso q 8)))))
