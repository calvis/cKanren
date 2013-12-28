#lang racket/base

(require 
 racket/base 
 "../ck.rkt"
 "../tree-unify.rkt"
 "../unstable/sets.rkt"
 "../tester.rkt")

(provide test-sets test-sets-long)

(define (test-sets)
  (let ([n (set-var 'n)])
    (test (normalize (set '() n)) n))
  
  (test (normalize (set '(bird cat) (set '() (empty-set))))
        (set '(bird cat) (empty-set)))
  
  (test (run* (q) (seto q)) '(s.0))

   (test (run* (q) (== (empty-set) (empty-set)))
         '(_.0))
   
   (test (run* (q) (== (make-set '(1)) (make-set '(1))))
         '(_.0))
 
   (test (run* (q) (== (empty-set) 5))
         '())
 
   (test (run* (q) (== 5 (empty-set)))
         '())
 
   (test (run* (q) (== (make-set '(1)) 5))
         '())
 
   (test (run* (q) (== 5 (make-set '(1))))
         '())
 
   (test (run* (q) (== (make-set '(1)) (empty-set)))
         '())
   
   (test (run* (q) (== (make-set '(1)) (make-set '(2))))
         '())
  
   (test (run* (q) (== (make-set '(2)) (make-set '(1))))
         '())
   
   (test (run* (q) (== q (empty-set)))
         `(,(empty-set)))
   
   (test (run* (q) (== (empty-set) q))
         `(,(empty-set)))

  (test (run* (q) (== q (make-set '(1 2))))
        `(,(make-set '(1 2))))

  (test (run* (q) 
          (== q (make-set '(1)))
          (== q (make-set '(2))))
        '())
  
   (test (run* (q) (== q (set '(1) q)))
         `([,(set '(1) 's.0) : (!in (1 s.0))]))

  (test (run* (q) (== (set '(1) q) q))
        `([,(set '(1) 's.0) : (!in (1 s.0))]))

  (test (run* (q) (fresh (z) (== q (set `(,z) q))))
        `((,(set '(_.0) 's.1) : (!in (_.0 s.1)))))
  
  (test (run* (q) (fresh (z) (== q (set '(1) z))))
        `(,(set '(1) 's.0)))

  (test (run* (q) (fresh (z) (== q (set `(,(set '(1) z)) q))))
        `(,(set `(,(set '(1) 's.0)) 's.1)))

  (test (run* (q) 
          (== (set `(1) q) (set `(2) (empty-set))))
        '())

  ;; Wrong?
  (test (run* (q)
          (seto q)
          (enforce-lazy-unify-same (set `(1) q) (set `(1) q)))
        '((s.0 : (!in (1 s.0)))))

  (test (run* (q)
          (seto q)
          (enforce-lazy-unify-same (set `(1) q) (set `(2) q)))
        `((,(set '(1 2) 's.0) : (!in (1 s.0) (2 s.0)))))

  (test (run* (q) 
          (== (set `(1) q) (set `(2) q)))
        `((,(set `(1 2) `s.0) : (!in (1 s.0) (2 s.0)))))

  (test (run* (q) 
          (fresh (x y r s) 
            (== (set `(1) r) (set `(2) s))))
        '(_.0))

  (test (run 1 (q) 
          (fresh (x y r)
            (== (set `(,x) r) (set `(,y) r))))
        '(_.0))
  
  (test (run* (q)
          (== q (set '() (set '(1) q))))
        `((,(set `(1) `s.0) : (!in (1 s.0)))))

  (test (run* (q)
          (== (set '() q) (set '() q)))
        '(s.0))

  (test (run* (q)
          (== q (set '() q)))
        '(s.0))

  (test (run* (q)
          (== (set '() (set '() q)) (set '() q)))
        '(s.0))

  (test (run* (q)
          (== (set `(1) (set `(2) (empty-set)))
              (set `(2) (set `(1) (empty-set)))))
        `(_.0))

  (test (run* (x r y s) 
          (== (set `(,x) r) (set `(,y) s)))
        `((_.0 s.1 _.0 s.1)
          ((_.0 ,(set `(_.1) `s.2) _.1 ,(set `(_.0) `s.2)) : (!in (_.0 s.2) (_.1 s.2)))
          ((_.0 s.1 _.0 ,(set `(_.0) `s.1)) : (!in (_.0 s.1)))
          ((_.0 ,(set `(_.0) `s.1) _.0 s.1) : (!in (_.0 s.1)))))

  ;; TODO
  (test (run* (q) 
          (fresh (y r s) 
            (== (set `(,q) r) (set `(,y) s))))
        '(_.0 _.0 _.0 _.0))

  (test (run* (q)
          (=/= (empty-set) (empty-set)))
        '())

  (test (run* (q)
          (=/= (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test (run* (q) (=/= q (empty-set)))
        `((_.0 : (=/= (_.0 . ,(empty-set))))))

  #;
  (test (run* (q) 
          (=/= q (set `(1) (set `(2) (empty-set)))))
        `((_.0 : (=/= (_.0 ,(make-set `(1 2)))))))

;;   (test (run* (q)
;;           (enforce-lazy-union-set
;;            (make-set '(1))
;;            (make-set '(2))
;;            (make-set '(1 2))))
;;         '(_.0))
;; 
;;   ;; Sanity checks
;;   (test (run* (q) (uniono (empty-set) (empty-set) (empty-set)))
;;         '(_.0))
;;   
;;   (test (run* (q)
;;           (fresh (x y z)
;;             (uniono (set `(1) (empty-set)) 
;;                     (set `(1) (empty-set))
;;                     (set `(1) (empty-set)))))
;;         '(_.0))
;; 
;;   (test (run* (q)
;;           (uniono (make-set '(1)) (make-set '(2)) (make-set '(1 2))))
;;         '(_.0))
;; 
;;   (test (run* (q)
;;           (uniono (make-set '(1)) (make-set '(2)) (make-set '(3))))
;;         '())
;; 
;;   (test (run* (q)
;;           (uniono q (make-set '(2)) (make-set '(1 2))))
;;         `(,(make-set `(1 2)) 
;;           ,(make-set `(1))))
;; 
;;   (test (run* (q)
;;           (uniono (make-set '(1)) q (make-set '(1 2))))
;;         `(,(make-set `(2)) 
;;           ,(make-set `(1 2))))
;;   
;;   (test (run* (q)
;;           (uniono (make-set '(1)) (make-set '(2)) q))
;;         `(,(make-set `(1 2))))

  #;
  (test
   (run 1 (x y z v)
     (uniono (make-set `(,x)) (set `(,y) z) v))
   `(((_.0 _.1 s.2 ,(set `(_.0 _.1) `s.2)) 
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 . _.1)))))
  
  #;
  (test-any-order
   (run 4 (x y z v)
     (uniono (make-set `(,x)) (set `(,y) z) v))
   `(((_.0 _.1 s.2 ,(set `(_.0 _.1) `s.2)) 
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 . _.1)))
     ((_.0 _.0 s.1 ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((_.0 _.0 ,(set `(_.0) `s.1) ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((_.0 _.1 ,(set `(_.0) `s.2) ,(set `(_.0 _.1) `s.2))
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 . _.1)))))

  (printf "================================================================\n")
  (test-any-order
   (run 5 (q)
     (fresh (x y z v)
       (== q `(,(make-set `(,x)) ,(set `(,y) z) ,v))
       (uniono (make-set `(,x)) (set `(,y) z) v)))
   `(((,(make-set `(_.0)) ,(set `(_.1) `s.2) ,(set `(_.0 _.1) `s.2))
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 . _.1)))
     ((,(make-set `(_.0)) ,(set `(_.0) `s.1) ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((,(make-set `(_.0)) ,(set `(_.0) `s.1) ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((,(make-set `(_.0)) ,(set `(_.0 _.1) `s.2) ,(set `(_.0 _.1) `s.2))
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 . _.1)))))

  #;
  (test-any-order
   (run* (x y z v)
     (uniono (make-set `(,x)) (set `(,y) z) v) prt)
   `(((_.0 _.1 s.2 ,(set `(_.0 _.1) `s.2)) 
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1)))
     ((_.0 _.0 ,(set `(_.0) `s.1) ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((_.0 _.0 s.1 ,(set `(_.0) `s.1))
      : (!in (_.0 s.1)))
     ((_.0 _.1 ,(set `(_.0) `s.2) ,(set `(_.0 _.1) `s.2))
      : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1)))))
  
;;   (test "test 31"
;;         (run* (q)
;;           (fresh (x y)
;;             (== q (make-set `(,x ,y)))
;;             (== (make-set `(,x ,y)) (make-set '(cat bird)))))
;;         `(,(make-set `(bird cat)) ,(make-set `(bird cat))))
;; 
;;   ;; Wrong?
;;   (test-any-order
;;    "test 32.15"
;;    (run* (q)
;;      (fresh (x y)
;;        (uniono (make-set `(cat ,x)) (make-set `(bird ,y)) q)))
;;    `((,(make-set `(_.0 bird cat)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
;;      (,(make-set `(_.0 _.1 bird cat))
;;       : (=/= (_.0 _.1)) (=/= ((_.0 . bird)) ((_.0 . cat)) ((_.1 . bird)) ((_.1 . cat))))
;;      ,(make-set `(bird cat))
;;      (,(make-set `(_.0 bird cat)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
;;      (,(make-set `(_.0 bird cat)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
;;      ,(make-set `(bird cat))))
;;   
;;   (test "enforce-lazy-union-var 1"
;;         (run* (q)
;;           (enforce-lazy-union-var
;;            (build-oc
;;             lazy-union-var
;;             (make-set '(dog))
;;             (make-set '(dog))
;;             q)))
;;         `(,(make-set `(dog))))
;; 
;;   (test "enforce-lazy-union-var 2"
;;         (run* (q)
;;           (enforce-lazy-union-var
;;            (build-oc
;;             lazy-union-var
;;             (make-set '(dog cat))
;;             (make-set '(dog cat))
;;             q)))
;;         `(,(make-set `(cat dog))))
;; 
;;   (test "enforce-lazy-union-var 3"
;;         (run* (q)
;;           (enforce-lazy-union-var
;;            (build-oc
;;             lazy-union-var
;;             (make-set '(cat dog))
;;             (make-set '(dog cat))
;;             q)))
;;         `(,(make-set `(cat dog))))
;; 
;;   (test "enforce-lazy-union-var 4"
;;         (run* (q)
;;           (enforce-lazy-union-var
;;            (build-oc
;;             lazy-union-var
;;             (make-set '(cat dog bird))
;;             (make-set '(bird dog cat))
;;             q)))
;;         `(,(make-set `(bird cat dog))))
;;   
;;   (test-any-order
;;    "union fresh 1"
;;    (run* (q)
;;      (fresh (x y z)
;;        (== q `(,x ,y ,z))
;;        (uniono x y z)
;;        (=/= z (empty-set))))
;;    `(((,(set `(_.0) `s.1) s.2 ,(set `(_.0) `s.3)) 
;;       : (!in (_.0 s.1) (_.0 s.3)) (union (s.1 s.2 s.3)))
;;      ((s.0 ,(set `(_.1) `s.2) ,(set `(_.1) `s.3)) 
;;       : (!in (_.1 s.2) (_.1 s.3)) (union (s.0 s.2 s.3)))
;;      ((,(set `(_.0) `s.1) ,(set `(_.0) `s.2) ,(set `(_.0) `s.3)) 
;;       : (!in (_.0 s.1) (_.0 s.2) (_.0 s.3)) (union (s.1 s.2 s.3)))))
;;   
;;   (test "empty uniono"
;;         (run* (q) (fresh (x y) (== q `(,x ,y)) (uniono x y (empty-set))))
;;         `((,(empty-set) ,(empty-set))))
;; 
;;   (test-any-order
;;    "union fresh 2"
;;    (run* (q)
;;      (fresh (x y z)
;;        (== q `(,x ,y ,z))
;;        (uniono x y z)))
;;    `((,(empty-set) ,(empty-set) ,(empty-set))
;;      ((,(set `(_.0) `s.1) s.2 ,(set `(_.0) `s.3)) 
;;       : (!in (_.0 s.1) (_.0 s.3)) (union (s.1 s.2 s.3)))
;;      ((s.0 ,(set `(_.1) `s.2) ,(set `(_.1) `s.3)) 
;;       : (!in (_.1 s.2) (_.1 s.3)) (union (s.0 s.2 s.3)))
;;      ((,(set `(_.0) `s.1) ,(set `(_.0) `s.2) ,(set `(_.0) `s.3)) 
;;       : (!in (_.0 s.1) (_.0 s.2) (_.0 s.3)) (union (s.1 s.2 s.3)))))
;; 
;;   (test "david's example"
;;         (time
;;          (length
;;           (run* (q)
;;             (fresh (x y z a b s s^)
;;               (== q s^)
;;               (uniono (make-set `(cat ,x ,y)) (make-set `(dog bird ,z)) s)
;;               (uniono s (make-set `(zebra ,a ,b)) s^)
;;               (== x 'dog)
;;               (== y 'bird)
;;               (== z 'cat)))))
;;         (length
;;          (run* (q)
;;            (fresh (x y z a b s s^)
;;              (== q s^)
;;              (uniono (make-set `(cat dog bird)) (make-set `(dog bird cat)) s)
;;              (uniono s (make-set `(zebra ,a ,b)) s^)))))
;; 
;;   ;; disj
;; 
;;   (test "disjo 1"
;;         (run* (q) (disjo (empty-set) (empty-set)))
;;         '(_.0))
;; 
;;   (test "disjo 2"
;;         (run* (q) (disjo (empty-set) (set '(1) (empty-set))))
;;         '(_.0))
;; 
;;   (test "disjo 3"
;;         (run* (q) (disjo (empty-set) q))
;;         '(s.0))
;; 
;;   (test "disjo 4"
;;         (run* (q) (disjo (set '(1) (empty-set)) (set '(1) (empty-set))))
;;         '())
;;   
;;   (test "disjo 5"
;;         (run* (x y z)
;;           (disjo (make-set `(,x ,y)) (set '(a) z)))
;;         '(((_.0 _.1 s.2) : (!in (_.0 s.2) (_.1 s.2)) (=/= ((_.0 . a)) ((_.1 . a))))))
;; 
;;   (test-any-order
;;    "disjo 6"
;;    (run* (x y) (disjo x y))
;;    ;; ((∅ ∅) ((∅ s.0) : (=/= (s.0 ∅))) ((s.0 ∅) : (=/= (s.0 ∅))) (({ _.0 | s.1 } { _.2 | s.3 }) : (!in (_.0 s.3) (_.2 s.1)) (=/= (_.0 _.2)) (disj (s.1 s.3))))
;;    `((,(empty-set) ,(empty-set))
;;      ((,(empty-set) s.0) : (=/= (s.0 ,(empty-set))))
;;      ((s.0 ,(empty-set)) : (=/= (s.0 ,(empty-set))))
;;      ((,(set '(_.0) 's.1) ,(set '(_.2) 's.3)) 
;;       : 
;;       (!in (_.0 s.3) (_.2 s.1)) 
;;       (=/= (_.0 _.2))
;;       (disj (s.1 s.3)))))
;; 
;;   ;; !uniono
;; 
;;   (test "!uniono 1"
;;         (run* (q)
;;           (!uniono (empty-set) (empty-set) (set '(1) (empty-set))))
;;         '(_.0))
;; 
;;   (test "!uniono 2"
;;         (run* (q)
;;           (!uniono (empty-set) (empty-set) (empty-set)))
;;         '())
;; 
;;   (test "ino"
;;         (run* (q)
;;           (ino q (set '(a b) (empty-set))))
;;         '(a b))
;; 
;;   (test "!ino 1"
;;         (run* (q)
;;           (!ino q (set '(a b) (empty-set))))
;;         '((_.0 : (=/= ((_.0 . a)) ((_.0 . b))))))
;; 
;;   (test "!uniono 3"
;;         (run* (q) 
;;           (!uniono (set `(x) (empty-set))
;;                    (set `(y) (empty-set))
;;                    (set `(,q) (empty-set))))
;;         '((_.0 : (=/= ((_.0 . x))))
;;           (_.0 : (=/= ((_.0 . y))))
;;           (_.0 : (=/= ((_.0 . x)) ((_.0 . y))))))
;; 
;;   (test "!uniono 4"
;;         (run 1 (q)
;;           (fresh (x y)
;;             (== q `(,x ,y))
;;             (!uniono x y (set `(a b) (empty-set)))))
;;         '(((s.0 s.1) : (!in (a s.0) (a s.1)))))
;; 
;;   (test-any-order
;;    "!uniono 5"
;;    (run 5 (q)
;;      (fresh (x y)
;;        (!uniono q (empty-set) (set `(a b) (empty-set)))))
;;    `((s.0 : (!in (a s.0)))
;;      (,(set `(_.0) `s.1) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
;;      (s.0 : (!in (b s.0)))))
;;   
;;   (test-any-order
;;    "!uniono 6"
;;    (run 5 (q)
;;      (fresh (x y)
;;        (== q `(,x ,y))
;;        (!uniono x y (set `(a b) (empty-set)))))
;;    `(((s.0 s.1) : (!in (a s.0) (a s.1)))
;;      ((s.0 s.1) : (!in (b s.0) (b s.1)))
;;      ((,(set `(_.0) `s.1) s.2) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
;;      ((s.0 ,(set `(_.1) `s.2)) : (!in (_.1 s.2)) (=/= ((_.1 . a)) ((_.1 . b))))))
;; 
;;   (test-any-order
;;    "!uniono 7"
;;    (run* (q)
;;      (fresh (x y)
;;        (== q `(,x ,y))
;;        (!uniono x y (set `(a b) (empty-set)))))
;;    `(((s.0 s.1) : (!in (a s.0) (a s.1)))
;;      ((s.0 s.1) : (!in (b s.0) (b s.1)))
;;      ((,(set `(_.0) `s.1) s.2) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
;;      ((s.0 ,(set `(_.1) `s.2)) : (!in (_.1 s.2)) (=/= ((_.1 . a)) ((_.1 . b))))))
;; 
;;   (test-any-order
;;    "union-disjo-1"
;;    (run* (x y z)
;;      (== y (make-set `(1)))
;;      (uniono x z (make-set `(1)))
;;      (uniono y z (make-set `(1)))
;;      (disjo x y))
;;    `((,(empty-set) ,(make-set '(1)) ,(make-set '(1)))))
;; 
;;   (test-any-order
;;    "union-disjo-2"
;;    (run* (x y z)
;;      (uniono x z (make-set `(1)))
;;      (uniono y z (make-set `(1)))
;;      (disjo x y))
;;    `((,(empty-set) ,(empty-set) ,(make-set '(1)))
;;      (,(empty-set) ,(make-set '(1)) ,(make-set '(1)))
;;      (,(make-set '(1)) ,(empty-set) ,(make-set '(1)))))
;; 
;;   #;
;;   (test
;;    "union-disjo-3"
;;    (run* (q)
;;      (fresh (R^ S^)
;;        (uniono R^ q (make-set '(1)))
;;        (uniono S^ q (make-set '(1)))
;;        (disjo R^ S^)
;;        (disjo R^ q)
;;        (disjo S^ q)))
;;    `(,(make-set '(1))))
;; 
;;   (let ()
;;     (define intersectiono
;;       (lambda (R S T)
;;         (fresh (R^ S^)
;;           (uniono R^ T R)
;;           (uniono S^ T S)
;;           (disjo S^ T)
;;           (disjo R^ T)
;;           (disjo R^ S^))))
;;     
;;     (test
;;      "intersectiono-1"
;;      (run* (q)
;;        (fresh (x y)
;;          (== x (make-set '()))
;;          (== y (make-set '()))
;;          (intersectiono x y q)))
;;      `(,(empty-set)))
;; 
;;     (test
;;      "intersectiono-2"
;;      (run* (q)
;;        (intersectiono (make-set '(1)) (make-set '(1)) q))
;;      `(,(make-set '(1))))
;;     
;;     #;
;;     (test
;;      "intersectiono-3"
;;      (run* (q)
;;        (intersectiono (make-set '(1 2)) (make-set '(2 3)) q))
;;      `(,(make-set '(2))))
;; 
;;     #;
;;     (test
;;      "intersectiono-4"
;;      (run* (q)
;;        (intersectiono (make-set '(1 2 3)) (make-set '(2 3 4)) q))
;;      `(,(make-set '(2 3))))
;; 
;;     #;
;;     (test
;;      "intersectiono-5"
;;      (run* (q)
;;        (fresh (x y)
;;          (== x (make-set '(1 2 3 4 5 6)))
;;          (== y (make-set '(2 3 5 7 9)))
;;          (intersectiono x y q)))
;;      `(,(make-set '(2 3 5)))))
;; 
  )

(define (test-sets-long)
  (test-sets))

(module+ main
  (test-sets-long))

