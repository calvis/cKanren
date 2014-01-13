#lang racket

(require 
 "../ck.rkt"
 "../tree-unify.rkt"
 "../unstable/fd.rkt"
 "../tester.rkt")

(provide test-fd test-fd-long)

;; (define add-digitso
;;   (lambda (augend addend carry-in carry digit)
;;     (fresh (partial-sum sum)
;;            (infd partial-sum (range 0 18))
;;            (infd sum (range 0 19))
;;            (plusfd augend addend partial-sum)
;;            (plusfd partial-sum carry-in sum)
;;            (conde
;;             ((<fd 9 sum) (=fd carry 1) (plusfd digit 10 sum))
;;             ((<=fd sum 9) (=fd carry 0) (=fd digit sum))))))
;; 
;; (define send-more-moneyo
;;   (lambda (letters)
;;     (fresh (s e n d m o r y carry0 carry1 carry2)
;;            (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
;;            (distinctfd letters)
;;            (infd s m (range 1 9))
;;            (infd e n d o r y (range 0 9))
;;            (infd carry0 carry1 carry2 (range 0 1))      
;;            (add-digitso s m carry2 m o)
;;            (add-digitso e o carry1 carry2 n)
;;            (add-digitso n r carry0 carry1 e)
;;            (add-digitso d e 0 carry0 y))))
;; 
;; (define diagonalso
;;   (lambda (n l)
;;     (let loop ((r l) (s (cdr l)) (i 0) (j 1))
;;       (cond
;;         ((or (null? r) (null? (cdr r))) succeed)
;;         ((null? s) (loop (cdr r) (cddr r) (+ i 1) (+ i 2)))
;;         (else
;;          (let ((qi (car r)) (qj (car s)))
;;            (conj
;;             (diago qi qj (- j i) (range 0 (* 2 n)))
;;             (loop r (cdr s) i (+ j 1)))))))))
;; 
;; (define diago
;;   (lambda (qi qj d rng)
;;     (fresh (qi+d qj+d)
;;            (infd qi+d qj+d rng)
;;            (plusfd qi d qi+d)
;;            (=/=fd qi+d qj)
;;            (plusfd qj d qj+d)
;;            (=/=fd qj+d qi))))
;; 
;; (define n-queenso
;;   (lambda (q* n)
;;     (let loop ((i n) (l '()))
;;       (cond
;;         ((zero? i)
;;          (conj
;;           (distinctfd l)
;;           (diagonalso n l)
;;           (== q* l)))
;;         (else (fresh (x)
;;                      (infd x (range 1 n))
;;                      (loop (- i 1) (cons x l))))))))
;; 
;; (define smm-mult
;;   (lambda (letters)
;;     (fresh (s e n d m o r y send more money)
;;            (== letters `(,s ,e ,n ,d ,m ,o ,r ,y))
;;            (distinctfd letters)
;;            (infd s m (range 1 9))
;;            (infd e n d o r y (range 0 9))
;;            (infd send more (range 0 9999))
;;            (infd money (range 0 99999))
;;            (actual-wortho `(,s ,e ,n ,d) send)
;;            (actual-wortho `(,m ,o ,r ,e) more)
;;            (actual-wortho `(,m ,o ,n ,e ,y) money)
;;            (plusfd send more money))))
;; 
;; (define actual-wortho
;;   (lambda (ls out)
;;     (let loop ((ls (reverse ls)) (place 1) (acc 0))
;;       (cond
;;         ((null? ls)
;;          (== acc out))
;;         (else
;;          (fresh (cur acc^)
;;                 (infd acc^ (range 0 (max-val place)))
;;                 (infd cur (range 0 (- (* place 10) 1)))
;;                 (timesfd (car ls) place cur)
;;                 (plusfd acc cur acc^)
;;                 (loop (cdr ls) (* place 10) acc^)))))))
;; 
;; (define max-val
;;   (lambda (n)
;;     (case n
;;       ((1) 9)
;;       ((10) 99)
;;       ((100) 999)
;;       ((1000) 9999)
;;       ((10000) 99999))))

(define (test-fd)
  
  (test (run* (x) (infd x '(1 2))) 
        '(1 2))
  
  (test (run* (x) (fresh (y) (infd x y '(1 2))))
        '(1 2))
  
  (test
   (run* (x)
     (fresh (y)
       (infd x y '(1 2))
       (=fd x y)))
   '(1 2))
  
  (test
   (run* (x)
     (infd x '(1 2))
     (=/=fd x 1))
   `(2))

  (test
   (run* (x)
     (infd x '(1 2))
     (=/=fd 1 x))
   `(2))
  
  (test
   (run* (q)
     (fresh (x)
       (infd x q '(1 2))
       (=/=fd x 1)
       (=fd x q)))
   `(2))

  (test
   (run* (x y z)
     (infd x '(1 2 3))
     (infd y '(3 4 5))
     (=fd x y)
     (infd z '(1 3 5 7 8))
     (infd z '(5 6))
     (=fd z 5))
   `((3 3 5)))
  
  (test
   (run* (x y z)
     (infd x '(1 2 3))
     (infd y '(3 4 5))
     (=fd x y)
     (infd z '(1 3 5 7 8))
     (infd z '(5 6))
     (=fd z x))
   '())
  
  (test
   (run* (q)
     (fresh (x y z) 
       (infd x '(1 2))
       (infd y '(2 3))
       (infd z q '(2 4))
       (=fd x y)
       (=/=fd x z)
       (=fd q z)))
   `(4))
  
  (test
   (run* (q)
     (fresh (x y z) 
       (=fd x y)
       (infd y '(2 3))
       (=/=fd x z)
       (infd z q '(2 4))
       (=fd q z)
       (infd x '(1 2))))
   `(4))
  
  (test
   (run* (x y)
     (infd x '(1 2))
     (infd y '(2 3))
     (=fd x y))
   `((2 2)))
  

  (test
   (run* (q)
     (fresh (x y z)
       (infd x y z '(1 2))
       (=/=fd x y)
       (=/=fd x z)
       (=/=fd y z)))
   `())
  
  (test
   (run* (q)
     (fresh (x) (infd x '(1 2)))
     (infd q '(5)))
   `(5))
  
  (test
   (run* (q)
     (infd q '(1 2))
     (== q #t))
   `())
  
  (test
   (run* (q)
     (== q #t)
     (infd q '(1 2)))
   `())
  
  (test
   (run* (q)
     (infd q (range 0 10))
     (<=fd q 5))
   `(0 1 2 3 4 5))
  
  (test
   (run* (q)
     (fresh (x)
       (infd x q (range 0 10))
       (<=fd x 5)
       (=fd q x)))
   `(0 1 2 3 4 5))
  
  (test
   (run* (q)
     (fresh (x)
       (<=fd x 5)
       (infd x q (range 0 10))
       (=fd q x)))
   `(0 1 2 3 4 5))
  
  (test
   (run* (x y)
     (infd x '(1 2 3))
     (infd y '(0 1 2 3 4))
     (<=fd x y))
   `((1 1) (1 2) (1 3) (1 4) (2 2) (2 3) (3 3) (2 4) (3 4)))
  
  (test
   (run* (x y)
     (infd x '(1 2 3))
     (infd y '(0 1 2 3 4))
     (<fd x y))
   `((1 2) (1 3) (1 4) (2 3) (2 4) (3 4)))
  
  (test
   (run* (x y)
     (infd x '(1 2 3))
     (infd y '(0 1 2 3 4))
     (<fd x y)
     (=/=fd x 1)
     (=fd y 3))
   `((2 3)))

  #;
  (test
   (run* (x y z)
     (infd x y z (range 0 3))
     (plusfd x y z))
   'error)
  
  #;
  (test
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
  
;;   (test
;;               (run* (q)
;;                     (distinctfd `(1 2 3 4 5)))
;;               `(_.0))
;;   
;;   (test
;;               (run* (q)
;;                     (distinctfd `(1 2 3 4 4 5)))
;;               `())
;;   
;;   (test
;;               (run* (q)
;;                     (infd q (range 0 2))
;;                     (distinctfd `(,q)))
;;               `(0 1 2))
;;   
;;   (test
;;               (run* (q)
;;                     (infd q (range 0 2))
;;                     (distinctfd `(,q ,q)))
;;               `())
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y z)
;;                            (infd x y z (range 0 2))
;;                            (distinctfd `(,x ,y ,z))
;;                            (== q `(,x ,y ,z))))
;;               `((0 1 2) (0 2 1) (1 0 2) (2 0 1) (1 2 0) (2 1 0)))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (a b c x)
;;                            (infd a b c (range 1 3))
;;                            (distinctfd `(,a ,b ,c))
;;                            (=/=fd c x)
;;                            (<=fd b 2)
;;                            (== x 3)
;;                            (== q `(,a ,b ,c))))
;;               '((3 1 2) (3 2 1)))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y z)
;;                            (infd x y z '(1 2))
;;                            (distinctfd `(,x ,y ,z))))
;;               '())
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y)
;;                            (infd x y (range 0 6))
;;                            (timesfd x y 6)
;;                            (== q `(,x ,y))))
;;               `((1 6) (2 3) (3 2) (6 1)))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y)
;;                            (infd x y (range 0 6))
;;                            (timesfd x 6 y)
;;                            (== q `(,x ,y))))
;;               `((0 0) (1 6)))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y)
;;                            (infd x y (range 0 6))
;;                            (timesfd 6 x y)
;;                            (== q `(,x ,y))))
;;               `((0 0) (1 6)))
;;   
;;   (test
;;               (run* (q)
;;                     (infd q (range 0 36))
;;                     (timesfd q q 36))
;;               `(6))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y)
;;                            (infd x y (range 1 100))
;;                            (timesfd x y 0)
;;                            (== q 5)))
;;               `())
;;   
;;   ;;; 34 + 89
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (digit1 digit2 carry0 carry1)
;;                            (infd carry0 carry1 (range 0 1))
;;                            (infd digit1 digit2 (range 0 9))
;;                            (add-digitso 4 9 0 carry0 digit1)
;;                            (add-digitso 3 8 carry0 carry1 digit2)
;;                            (== q `(,carry1 ,digit2 ,digit1))))
;;               '((1 2 3)))
;;   
;;   ;;; ((1 2 3))
;;   
;;   (display "Send More Money (addition)\n")
;;   (display (time (run* (q) (send-more-moneyo q))))
;;   (newline)
;;   
;;   (display "One Solution for Eight Queens\n")
;;   (display (time (run 1 (q) (n-queenso q 8))))
;;   (newline)
;;   
;;   (test
;;               (run* (q)
;;                     (actual-wortho `(1 2 3) 123))
;;               `(_.0))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x y z)
;;                            (infd x y z (range 0 9))
;;                            (== q `(,x ,y ,z))
;;                            (actual-wortho `(,x ,y ,z) 123)))
;;               `((1 2 3)))
;;   
;;   (test
;;               (run* (q)
;;                     (infd q (range 0 999))
;;                     (actual-wortho `(1 2 3) q))
;;               `(123))
;;   
;;   (test
;;               (run* (q)
;;                     (infd q (range 0 9))
;;                     (actual-wortho `(5 ,q 3) 543))
;;               `(4))
;;   
;;   (test
;;               (run* (q)
;;                     (fresh (x)
;;                            (infd x (range 0 9))
;;                            (infd q (range 0 999))
;;                            (actual-wortho `(5 ,x 3) q)))
;;               `(503 513 523 533 543 553 563 573 583 593))
  
)

(define (test-fd-long)
  (test-fd)
;;   (display "All Solutions for Eight Queens\n")
;;   (display (time (length (run* (q) (n-queenso q 8)))))
;;   (newline)
;;   
;;   (display "Send More Money (multiplication)\n")
;;   (display (time (run* (q) (smm-mult q))))
;;   (newline)
)

(module+ main
  (test-fd-long)
  )
