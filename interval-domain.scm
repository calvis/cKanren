(library
  (interval-domain)
  (export range value-dom?
    map-sum null-dom? singleton-dom? singleton-element-dom
    min-dom max-dom memv-dom? intersection-dom diff-dom
    copy-before drop-before disjoint-dom? make-dom

    interval-difference interval-union interval-intersection
    interval-memq? cons-dom interval-overlap? interval-> interval-<)
  (import (rnrs) (ck) (only (chezscheme) trace-define))

;;; domains (sorted lists of integers)

(define range
  (lambda (lb ub)
    `((,lb . ,ub))))

(define value-dom?
  (lambda (v)
    (and (integer? v) (<= 0 v))))

(define interval?
  (lambda (x)
    (pair? x)))

(define interval-union
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
          (jmin (car j)) (jmax (cdr j)))
      (cond
        ;; [1 2][2 3] = [1 3]
        ;; [1 2][3 4]
        ((or (= imax jmin)
             (= imax (- jmin 1)))
         `((,imin . ,jmax)))
        ;; [2 3][1 2] = [1 3]
        ((or (= jmax imin)
             (= jmax (- imin 1)))
         `((,jmin . ,imax)))
        ;; [1 2][4 5] = ([1 2] [4 5])
        ((< imax jmin) `(,i ,j))
        ;; [4 5][1 2] = ([1 2] [4 5])
        ((< jmax imin) `(,j ,i))
        ;; [1 5][2 3] = [1 5]
        ((and (<= imin jmin) (>= imax jmax)) `((,imin . ,imax)))
        ;; [2 3][1 5] = [1 5]
        ((and (<= jmin imin) (>= jmax imax)) `((,jmin . ,jmax)))
        ;; [1 3][2 5] = [1 5]
        ((and (<= imin jmin) (>= jmax imax)) `((,imin . ,jmax)))
        ;; [2 5][1 3] = [1 5]
        ((and (<= jmin imin) (>= imax jmax)) `((,jmin . ,imax)))
        (else (error 'interval-union "Not written yet" i j))))))


(define interval-difference
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
          (jmin (car j)) (jmax (cdr j)))
      (cond
        ;; [1 2] - [3 4] = ([1 2])
        ((> jmin imax) `((,imin . ,imax)))
        ;; [2 3] - [1 5] = ()
        ((and (<= jmin imin) (>= jmax imax)) `())

        ;; At this point we know j nether misses i nor does it
        ;; completely envelop i.  There must be some overlap.

        ;; [1 5] - [2 3] = ([1 1] [4 5])
        ((and (< imin jmin) (> imax jmax))
         `((,imin . ,(- jmin 1)) (,(+ jmax 1) . ,imax)))
        ;; [1 3] - [2 4] = [1 1]
        ((and (< imin jmin) (<= jmin imax))
         `((,imin . ,(- jmin 1))))
        ;; [1 3] - [0 1] = [2 3]
        ((and (> imax jmax) (<= jmin imin))
         `((,(+ jmax 1) . ,imax)))

        (else (error 'interval-difference "Not written yet" i j))))))

(define interval-intersection
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
          (jmin (car j)) (jmax (cdr j)))
      (cond
        ;; [1 5][6 10] = ()
        ((< imax jmin) `())
        ;; [6 10][1 5] = ()
        ((< jmax imin) `())
        ;; [1 5][2 3] = ([2 3])
        ((and (<= imin jmin) (>= imax jmax)) `(,j))
        ;; [2 3][1 5] = ([2 3])
        ((and (<= jmin imin) (>= jmax imax)) `(,i))
        ;; [1 3][2 5] = ([2 3])
        ((and (<= imin jmin) (<= imax jmax))
         `((,jmin . ,imax)))
        ;; [2 5][1 3] = ([2 3])
        ((and (<= jmin imin) (<= jmax imax))
         `((,imin . ,jmax)))
        (else (error 'interval-intersection "Not written yet" i j))))))

(define interval-memq?
  (lambda (x intvl)
    (and (>= x (car intvl)) (<= x (cdr intvl)))))

;; n* should be a non-empty sorted (small to large) list
;; of value-doms?, with no duplicates.
(define make-dom
  (lambda (n*)
    (let loop ((n* n*))
      (cond
        ((null? n*) `())
        (else (cons-dom (car n*) (loop (cdr n*))))))))

;; lazy hack
(define interval-overlap?
  (lambda (i j)
    (null? (cdr (interval-union i j)))))

(define interval->
  (lambda (i j)
    (> (car i) (cdr j))))

(define interval-<
  (lambda (i j)
    (< (cdr i) (car j))))

(define car-dom
  (lambda (dom)
    (caar dom)))

(define cdr-dom
  (lambda (dom)
    (let ((intvl (car dom)))
      (if (singleton-interval? intvl)
          (cdr dom)
          (cons `(,(+ (car intvl) 1) . ,(cdr intvl)) (cdr dom))))))

(define cons-dom
  (lambda (x dom)
    (let loop ((x (if (interval? x) x `(,x . ,x))) (dom dom))
      (cond
        ((null? dom) `(,x))
        ((interval-overlap? x (car dom))
         (append-dom (interval-union x (car dom)) (cdr dom)))
        ((interval-> x (car dom))
         (cons-dom (car dom) (loop x (cdr dom))))
        (else (cons x dom))))))

(define append-dom
  (lambda (l s)
    (cond
      ((null? l) s)
      (else (cons-dom (car l) (append-dom (cdr l) s))))))

(define map-sum
  (lambda (f)
    (letrec
      ((loop
         (lambda (dom)
           (cond
             ((null? dom)
              (lambdag@ (a) (mzerog)))
             (else
               (conde
                 ((f (car-dom dom)))
                 ((loop (cdr-dom dom)))))))))
      loop)))

(define null-dom?
  (lambda (x)
    (null? x)))

(define singleton-interval?
  (lambda (x)
    (= (car x) (cdr x))))

(define singleton-dom?
  (lambda (dom)
    (and (null? (cdr dom))
         (singleton-interval? (car dom)))))

(define singleton-element-dom
  (lambda (dom)
    (caar dom)))

(define min-dom
  (lambda (dom)
    (caar dom)))

(define max-dom
  (lambda (dom)
    (cond
      ((null? (cdr dom)) (cdar dom))
      (else (max-dom (cdr dom))))))

(define memv-dom?
  (lambda (v dom)
    (and (value-dom? v)
         (exists (lambda (x) (interval-memq? v x)) dom))))

(define intersection-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) '())
      ;; ((< (car dom1) (car dom2))
      ;;  (intersection-dom (cdr dom1) dom2))
      ((interval-< (car dom1) (car dom2))
       (intersection-dom (cdr dom1) dom2))
      ;; (else (intersection-dom dom1 (cdr dom2)))
      ((interval-> (car dom1) (car dom2))
       (intersection-dom dom1 (cdr dom2)))
      ;; ((= (car dom1) (car dom2))
      ;;  (cons (car dom1)
      ;;    (intersection-dom (cdr dom1) (cdr dom2))))
      (else
        (append-dom
          (interval-intersection (car dom1) (car dom2))
          (intersection-dom
            (append-dom
              (interval-difference (car dom1) (car dom2))
              (cdr dom1))
            (append-dom
              (interval-difference (car dom2) (car dom1))
              (cdr dom2))))))))

;; ([1 2]) ([3 4])

(define diff-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) dom1)
      ;; ((< (car dom1) (car dom2))
      ;;  (cons (car dom1) (diff-dom (cdr dom1) dom2)))
      ((interval-< (car dom1) (car dom2))
       (cons (car dom1) (diff-dom (cdr dom1) dom2)))
      ;; (else (diff-dom dom1 (cdr dom2)))
      ((interval-> (car dom1) (car dom2))
       (diff-dom dom1 (cdr dom2)))
      ;; ((= (car dom1) (car dom2))
      ;;  (diff-dom (cdr dom1) (cdr dom2)))
      (else
       (diff-dom
         (append-dom
           (interval-difference (car dom1) (car dom2))
           (cdr dom1))
         dom2))
)))

(define copy-before   
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((pred (car-dom dom)) '())
      (else (cons-dom
              (car-dom dom)
              (copy-before pred (cdr-dom dom)))))))

(define drop-before
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((pred (car-dom dom)) dom)
      (else (drop-before pred (cdr-dom dom))))))

(define disjoint-dom?
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) #t)
      ;; ((< (car dom1) (car dom2))
      ;;  (disjoint-dom? (cdr dom1) dom2))
      ((interval-< (car dom1) (car dom2))
       (disjoint-dom? (cdr dom1) dom2))
      ;; (else (disjoint-dom? dom1 (cdr dom2)))
      ((interval-> (car dom1) (car dom2))
       (disjoint-dom? dom1 (cdr dom2)))
      ;; ((= (car dom1) (car dom2)) #f)
      (else #f))))

)

(import (interval-domain))

;; range
(assert (equal? (range 0 10) `((0 . 10))))

;; interval-overlap?
(assert (interval-overlap? `(1 . 3) `(2 . 4)))
(assert (not (interval-overlap? `(1 . 2) `(4 . 5))))

;; interval->
(assert (interval-> `(4 . 5) `(1 . 2)))
(assert (interval-> `(5 . 5) `(1 . 2)))
(assert (not (interval-> `(1 . 2) `(4 . 5))))
(assert (not (interval-> `(4 . 5) `(1 . 4))))

;; interval-<
(assert (not (interval-< `(4 . 5) `(1 . 2))))
(assert (not (interval-< `(5 . 5) `(1 . 2))))
(assert (interval-< `(1 . 2) `(4 . 5)))
(assert (not (interval-< `(4 . 5) `(1 . 4))))
(assert (interval-< `(1 . 2) `(3 . 9)))
(assert (not (interval-< `(4 . 5) `(3 . 9))))

;; interval-union
(assert (equal? (interval-union `(1 . 2) `(2 . 3)) `((1 . 3))))
(assert (equal? (interval-union `(2 . 3) `(1 . 2)) `((1 . 3))))
(assert (equal? (interval-union `(1 . 5) `(2 . 3)) `((1 . 5))))
(assert (equal? (interval-union `(2 . 3) `(1 . 5)) `((1 . 5))))
(assert (equal? (interval-union `(1 . 3) `(2 . 5)) `((1 . 5))))
(assert (equal? (interval-union `(2 . 5) `(1 . 3)) `((1 . 5))))
(assert (equal? (interval-union `(1 . 2) `(4 . 5)) `((1 . 2) (4 . 5))))
(assert (equal? (interval-union `(4 . 5) `(1 . 2)) `((1 . 2) (4 . 5))))
(assert (equal? (interval-union `(1 . 2) `(3 . 4)) `((1 . 4))))

;; interval-difference
(assert (equal? (interval-difference `(1 . 2) `(3 . 4)) `((1 . 2))))
(assert (equal? (interval-difference `(2 . 3) `(1 . 5)) `()))
(assert (equal? (interval-difference `(1 . 5) `(2 . 3)) `((1 . 1) (4 . 5))))
(assert (equal? (interval-difference `(1 . 3) `(3 . 4)) `((1 . 2))))
(assert (equal? (interval-difference `(1 . 3) `(0 . 1)) `((2 . 3))))
(assert (equal? (interval-difference `(3 . 10) `(1 . 5)) `((6 . 10))))
(assert (equal? (interval-difference `(1 . 6) `(3 . 10)) `((1 . 2))))

;; interval-memq?
(assert (interval-memq? 5 `(1 . 10)))
(assert (not (interval-memq? 11 `(1 . 10))))

;; cons-dom
(assert (equal? (cons-dom 5 `((1 . 2))) `((1 . 2) (5 . 5))))
(assert (equal? (cons-dom 3 `((4 . 5))) `((3 . 5))))
(assert (equal? (cons-dom 5 `((3 . 4))) `((3 . 5))))
(assert (equal? (cons-dom 3 `((1 . 2) (4 . 5))) `((1 . 5))))

;; difference-dom
(assert (equal? (diff-dom `((1 . 2)) `((4 . 5))) `((1 . 2))))
(assert (equal? (diff-dom `((1 . 10)) `((4 . 5))) `((1 . 3) (6 . 10))))
(assert (equal? (diff-dom `((1 . 6)) `((3 . 10))) `((1 . 2))))
(assert (equal? (diff-dom
                  `((1 . 2) (4 . 5) (7 . 10))
                  `((3 . 9)))
          `((1 . 2) (10 . 10))))
(assert (equal? (diff-dom
                  `((1 . 10))
                  `((2 . 3) (5 . 7)))
          `((1 . 1) (4 . 4) (8 . 10))))

;; interval-intersection
(assert (equal? (interval-intersection `(1 . 5) `(6 . 10)) `()))
(assert (equal? (interval-intersection `(6 . 10) `(1 . 5)) `()))
(assert (equal? (interval-intersection `(1 . 5) `(2 . 3)) `((2 . 3))))
(assert (equal? (interval-intersection `(2 . 3) `(1 . 5)) `((2 . 3))))
(assert (equal? (interval-intersection `(1 . 3) `(2 . 5)) `((2 . 3))))
(assert (equal? (interval-intersection `(2 . 5) `(1 . 3)) `((2 . 3))))

;; intersection-dom
(assert (equal? (intersection-dom `((1 . 5)) `((6 . 10))) `()))
(assert (equal? (intersection-dom `((6 . 10)) `((1 . 5))) `()))
(assert (equal? (intersection-dom `((1 . 6)) `((3 . 10))) `((3 . 6))))
(assert (equal? (intersection-dom `((3 . 10)) `((1 . 6))) `((3 . 6))))
(assert (equal?
          (intersection-dom
            `((1 . 2) (4 . 5) (7 . 8))
            `((3 . 9)))
          `((4 . 5) (7 . 8))))
(assert (equal?
          (intersection-dom
            `((3 . 9))
            `((1 . 2) (4 . 5) (7 . 8)))
          `((4 . 5) (7 . 8))))

(printf "Assertions passed!\n")

