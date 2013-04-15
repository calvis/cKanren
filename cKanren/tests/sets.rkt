#lang racket/base

(require 
 racket/base 
 "../ck.rkt"
 "../tree-unify.rkt"
 "../sets.rkt"
 "../tester.rkt")

(provide test-sets test-sets-long)

(define (test-sets)
  (let ([n (set-var 'n)])
    (test "normalize 1" (normalize (set '() n)) n))
  
  (test "normalize 2"
        (normalize (set '(bird cat) (set '() (empty-set))))
        (set '(bird cat) (empty-set)))

  (test "test 0.0" (run* (q) succeed)  '(_.0))
  (test "test 0.1" (run* (q) (== 5 5)) '(_.0))
  (test "test 0.2" (run* (q) (== 5 6)) '())
  (test "test 0.3" (run* (q) (fresh (x) (== q `(,x)))) '((_.0)))

  (test "test 0.4" (run* (q) (seto q)) '(s.0))

  (test "test 1"
        (run* (q) (== (empty-set) (empty-set)))
        '(_.0))

  (test "test 2" 
        (run* (q) (== (make-set '(1)) (make-set '(1))))
        '(_.0))

  (test "test 3.0"
        (run* (q) (== (empty-set) 5))
        '())

  (test "test 3.1"
        (run* (q) (== 5 (empty-set)))
        '())

  (test "test 4.0"
        (run* (q) (== (make-set '(1)) 5))
        '())

  (test "test 4.1"
        (run* (q) (== 5 (make-set '(1))))
        '())

  (test "test 5.0"
        (run* (q) (== (make-set '(1)) (empty-set)))
        '())

  (test "test 5.05"
        (run* (q) (== (make-set '(1)) (make-set '(2))))
        '())

  (test "test 5.1"
        (run* (q) (== (make-set '(2)) (make-set '(1))))
        '())

  (test "test 6.01"
        (run* (q) (== q (empty-set)))
        '(∅))

  (test "test 6.02"
        (run* (q) (== (empty-set) q))
        '(∅))

  (test "test 6.1"
        (run* (q) (== q (make-set '(1 2))))
        '((set (1 2 : ∅))))

  (test "test 7"
        (run* (q) 
          (== q (make-set '(1)))
          (== q (make-set '(2))))
        '())
  
  (test "test 8.0"
        (run* (q) (== q (set '(1) q)))
        `(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 8.1"
        (run* (q) (== (set '(1) q) q))
        `(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 9.0"
        (run* (q) (fresh (z) (== q (set `(,z) q))))
        '(((set (_.0 : s.1)) : (!in (_.0 s.1)))))

  (test "test 9.1"
        (run* (q) (fresh (z) (== q (set '(1) z))))
        '((set (1 : s.0))))

  (test "test 9.2"
        (run* (q) (fresh (z) (== q (set `(,(set '(1) z)) q))))
        '(((set ((set (1 : s.0)) : s.1)) : (!in ((set (1 : s.0)) s.1)))))

  (test "test 9.5"
        (run* (q) 
          (== (set `(1) q) (set `(2) (empty-set))))
        '())

  ;; Wrong?
  (test "enforce-lazy-unify-same 1"
        (run* (q)
          (seto q)
          (enforce-lazy-unify-same (build-oc lazy-unify-same (set `(1) q) (set `(1) q))))
        '((s.0 : (!in (1 s.0)))))

  (test "enforce-lazy-unify-same 2"
        (run* (q)
          (seto q)
          (enforce-lazy-unify-same (build-oc lazy-unify-same (set `(1) q) (set `(2) q))))
        '(((set (1 2 : s.0)) : (!in (1 s.0) (2 s.0)))))

  (test "test 10.0"
        (run* (q) 
          (== (set `(1) q) (set `(2) q)))
        '(((set (1 2 : s.0)) : (!in (1 s.0) (2 s.0)))))

  (test "test 10.01"
        (run* (q) 
          (fresh (x y r s) 
            (== (set `(1) r) (set `(2) s))))
        '(_.0))

  (test "test 10.05"
        (run 1 (q) 
          (fresh (x y r)
            (== (set `(,x) r) (set `(,y) r))))
        '(_.0))
  
  (test "test 10.06"
        (run* (q)
          (== q (set '() (set '(1) q))))
        '(((set (1 : s.0)) : (!in (1 s.0)))))

  (test "test 10.07"
        (run* (q)
          (== (set '() q) (set '() q)))
        '(s.0))

  (test "test 10.08" 
        (run* (q)
          (== q (set '() q)))
        '(s.0))

  (test "test 10.09"
        (run* (q)
          (== (set '() (set '() q)) (set '() q)))
        '(s.0))

  (test "test 9.iv.1"
        (run* (q)
          (== (set `(1) (set `(2) (empty-set)))
              (set `(2) (set `(1) (empty-set)))))
        `(_.0))

  (test "test 10.2"
        (run* (q) 
          (fresh (y r s) 
            (== (set `(,q) r) (set `(,y) s))))
        '(_.0 _.0 _.0 _.0))

  (test "test 10.3"
        (run* (q) 
          (fresh (x y r s) 
            (== q `(,x ,r ,y ,s))
            (== (set `(,x) r) (set `(,y) s))))
        '((_.0 s.1 _.0 s.1)
          ((_.0 (set (_.1 : s.2)) _.1 (set (_.0 : s.2))) : (!in (_.0 s.2) (_.1 s.2)))
          ((_.0 s.1 _.0 (set (_.0 : s.1))) : (!in (_.0 s.1)))
          ((_.0 (set (_.0 : s.1)) _.0 s.1) : (!in (_.0 s.1)))))

  (test "test 20"
        (run* (q)
          (=/= (empty-set) (empty-set)))
        '())

  (test "test 21"
        (run* (q)
          (=/= (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "test 22"
        (run* (q)
          (=/= q (empty-set)))
        '((_.0 : (=/= (_.0 ∅)))))

  (test "test 23"
        (run* (q) 
          (=/= q (set `(1) (set `(2) (empty-set)))))
        '((_.0 : (=/= (_.0 (set (1 2 : ∅)))))))

  (test "enforce-lazy-union-set"
        (run* (q)
          (enforce-lazy-union-set
           (build-oc lazy-union-set
                     (make-set '(1))
                     (make-set '(2))
                     (make-set '(1 2)))))
        '(_.0))

  ;; Sanity checks
  (test "sanity check 1"
        (run* (q) (uniono (empty-set) (empty-set) (empty-set)))
        '(_.0))
  
  (test "sanity check 2"
        (run* (q)
          (fresh (x y z)
            (uniono (set `(1) (empty-set)) 
                    (set `(1) (empty-set))
                    (set `(1) (empty-set)))))
        '(_.0))

  (test "test 26"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) (make-set '(1 2))))
        '(_.0))

  (test "test 27"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) (make-set '(3))))
        '())

  (test "test 28"
        (run* (q)
          (uniono q (make-set '(2)) (make-set '(1 2))))
        '((set (1 : ∅)) 
          (set (1 2 : ∅))))

  (test "test 29"
        (run* (q)
          (uniono (make-set '(1)) q (make-set '(1 2))))
        '((set (2 : ∅)) 
          (set (1 2 : ∅))))

  (test "test 30"
        (run* (q)
          (uniono (make-set '(1)) (make-set '(2)) q))
        '((set (1 2 : ∅))))

  (test "test 30.5"
        (run* (q) 
          (fresh (x y z v)
            (== q `(,x ,y ,z ,v))
            (uniono (make-set `(,x)) (set `(,y) z) v)))
        '(((_.0 _.1 s.2 (set (_.0 _.1 : s.2))) 
           : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1)))
          ((_.0 _.0 s.1 (set (_.0 : s.1)))
           : (!in (_.0 s.1)))
          ((_.0 _.1 (set (_.0 : s.2)) (set (_.0 _.1 : s.2)))
           : (!in (_.0 s.2) (_.1 s.2)) (=/= (_.0 _.1))) 
          ((_.0 _.0 (set (_.0 : s.1)) (set (_.0 : s.1)))
           : (!in (_.0 s.1)))))

  (test "test 31"
        (run* (q)
          (fresh (x y)
            (== q (make-set `(,x ,y)))
            (== (make-set `(,x ,y)) (make-set '(cat bird)))))
        '((set (bird cat : ∅)) (set (bird cat : ∅))))

  ;; Wrong?
  (test "test 32.15"
        (run* (q)
          (fresh (x y)
            (uniono (make-set `(cat ,x)) (make-set `(bird ,y)) q)))
        '(((set (bird cat _.1 _.0 : ∅)) 
           : (=/= (_.0 _.1)) (=/= ((_.0 . bird)) ((_.0 . cat)) ((_.1 . bird)) ((_.1 . cat))))
          ((set (bird cat _.0 : ∅)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
          (set (bird cat : ∅))
          ((set (bird cat _.0 : ∅)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
          ((set (bird cat _.0 : ∅)) : (=/= ((_.0 . bird)) ((_.0 . cat))))
          (set (bird cat : ∅))))

  (test "enforce-lazy-union-var 1"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(dog))
            (make-set '(dog))
            q)))
        '((set (dog : ∅))))

  (test "enforce-lazy-union-var 2"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(dog cat))
            (make-set '(dog cat))
            q)))
        '((set (cat dog : ∅))))

  (test "enforce-lazy-union-var 3"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(cat dog))
            (make-set '(dog cat))
            q)))
        '((set (cat dog : ∅))))

  (test "enforce-lazy-union-var 4"
        (run* (q)
          (enforce-lazy-union-var
           (build-oc
            lazy-union-var
            (make-set '(cat dog bird))
            (make-set '(bird dog cat))
            q)))
        '((set (bird cat dog : ∅))))
  
  (test "union fresh"
        (run* (q)
          (fresh (x y z)
            (== q `(,x ,y ,z))
            (uniono x y z)
            (=/= z (empty-set))))
        '((((set (_.0 : s.1)) s.2 (set (_.0 : s.3))) 
           : (!in (_.0 s.1) (_.0 s.3)) (union (s.1 s.2 s.3)))
          ((s.0 (set (_.1 : s.2)) (set (_.1 : s.3))) 
           : (!in (_.1 s.2) (_.1 s.3)) (union (s.0 s.2 s.3)))
          (((set (_.0 : s.1)) (set (_.0 : s.2)) (set (_.0 : s.3))) 
           : (!in (_.0 s.1) (_.0 s.2) (_.0 s.3)) (union (s.1 s.2 s.3)))))

  (test "david's example"
        (time
         (length
          (run* (q)
            (fresh (x y z a b s s^)
              (== q s^)
              (uniono (make-set `(cat ,x ,y)) (make-set `(dog bird ,z)) s)
              (uniono s (make-set `(zebra ,a ,b)) s^)
              (== x 'dog)
              (== y 'bird)
              (== z 'cat)))))
        (length
         (run* (q)
           (fresh (x y z a b s s^)
             (== q s^)
             (uniono (make-set `(cat dog bird)) (make-set `(dog bird cat)) s)
             (uniono s (make-set `(zebra ,a ,b)) s^)))))

  ;; disj

  (test "disjo 1"
        (run* (q) (disjo (empty-set) (empty-set)))
        '(_.0))

  (test "disjo 2"
        (run* (q) (disjo (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "disjo 3"
        (run* (q) (disjo (empty-set) q))
        '(s.0))

  (test "disjo 4"
        (run* (q) (disjo (set '(1) (empty-set)) (set '(1) (empty-set))))
        '())
  
  (test "test disjo 1"
        (run* (q)
          (fresh (x y z)
            (== q `(,x ,y ,z))
            (disjo (set `(,x ,y) (empty-set)) (set '(a) z))))
        '(((_.0 _.1 s.2) : (!in (_.1 s.2)) (=/= ((_.0 . a)) ((_.1 . a))))))

  ;; !uniono

  (test "!uniono 1"
        (run* (q)
          (!uniono (empty-set) (empty-set) (set '(1) (empty-set))))
        '(_.0))

  (test "!uniono 2"
        (run* (q)
          (!uniono (empty-set) (empty-set) (empty-set)))
        '())

  (test "ino"
        (run* (q)
          (ino q (set '(a b) (empty-set))))
        '(a b))

  (test "!ino 1"
        (run* (q)
          (!ino q (set '(a b) (empty-set))))
        '((_.0 : (=/= ((_.0 . a)) ((_.0 . b))))))

  (test "!uniono 3"
        (run* (q) 
          (!uniono (set `(x) (empty-set))
                   (set `(y) (empty-set))
                   (set `(,q) (empty-set))))
        '((_.0 : (=/= ((_.0 . x)) ((_.0 . y))))
          (_.0 : (=/= ((_.0 . x))))
          (_.0 : (=/= ((_.0 . y))))))

  (test "!uniono 4"
        (run 1 (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))))

  (test "!uniono 5"
        (run 5 (q)
          (fresh (x y)
            (!uniono q (empty-set) (set `(a b) (empty-set)))))
        '(((set (_.0 : s.1)) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
          (s.0 : (!in (a s.0)))
          (s.0 : (!in (b s.0)))))

  (test "!uniono 6"
        (run 5 (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))
          (((set (_.0 : s.1)) s.2) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
          ((s.0 (set (_.1 : s.2))) : (!in (_.1 s.2)) (=/= ((_.1 . a)) ((_.1 . b))))
          ((s.0 s.1) : (!in (b s.0) (b s.1)))))

  (test "!uniono 7"
        (run* (q)
          (fresh (x y)
            (== q `(,x ,y))
            (!uniono x y (set `(a b) (empty-set)))))
        '(((s.0 s.1) : (!in (a s.0) (a s.1)))
          (((set (_.0 : s.1)) s.2) : (!in (_.0 s.1)) (=/= ((_.0 . a)) ((_.0 . b))))
          ((s.0 (set (_.1 : s.2))) : (!in (_.1 s.2)) (=/= ((_.1 . a)) ((_.1 . b))))
          ((s.0 s.1) : (!in (b s.0) (b s.1)))))
  
  )

(define (test-sets-long)
  (test-sets))

(module+ main
  (test-sets-long))

