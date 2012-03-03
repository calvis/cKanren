(library
  (interval-domain)
  (export range value-dom?
    ;; for fd
    map-sum null-dom? singleton-dom? singleton-element-dom
    min-dom max-dom memv-dom? intersection-dom diff-dom
    copy-before-dom drop-before-dom disjoint-dom? make-dom

    ;; interval helpers
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
        ((or (= imax jmin)
             (= imax (- jmin 1)))
         `((,imin . ,jmax)))
        ((or (= jmax imin)
             (= jmax (- imin 1)))
         `((,jmin . ,imax)))
        ((< imax jmin) `(,i ,j))
        ((< jmax imin) `(,j ,i))
        ((and (<= imin jmin) (>= imax jmax)) `((,imin . ,imax)))
        ((and (<= jmin imin) (>= jmax imax)) `((,jmin . ,jmax)))
        ((and (<= imin jmin) (>= jmax imax)) `((,imin . ,jmax)))
        ((and (<= jmin imin) (>= imax jmax)) `((,jmin . ,imax)))
        (else (error 'interval-union "Not defined" i j))))))


(define interval-difference
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
          (jmin (car j)) (jmax (cdr j)))
      (cond
        ((> jmin imax) `((,imin . ,imax)))
        ((and (<= jmin imin) (>= jmax imax)) `())
        ((and (< imin jmin) (> imax jmax))
         `((,imin . ,(- jmin 1)) (,(+ jmax 1) . ,imax)))
        ((and (< imin jmin) (<= jmin imax))
         `((,imin . ,(- jmin 1))))
        ((and (> imax jmax) (<= jmin imin))
         `((,(+ jmax 1) . ,imax)))
        (else (error 'interval-difference "Not defined" i j))))))

(define interval-intersection
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
          (jmin (car j)) (jmax (cdr j)))
      (cond
        ((< imax jmin) `())
        ((< jmax imin) `())
        ((and (<= imin jmin) (>= imax jmax)) `(,j))
        ((and (<= jmin imin) (>= jmax imax)) `(,i))
        ((and (<= imin jmin) (<= imax jmax))
         `((,jmin . ,imax)))
        ((and (<= jmin imin) (<= jmax imax))
         `((,imin . ,jmax)))
        (else (error 'interval-intersection "Not defined" i j))))))

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
        ((null-dom? dom) `(,x))
        ((interval-overlap? x (car dom))
         (append-dom (interval-union x (car dom)) (cdr dom)))
        ((interval-> x (car dom))
         (cons-dom (car dom) (loop x (cdr dom))))
        (else (cons x dom))))))

(define append-dom
  (lambda (l s)
    (cond
      ((null-dom? l) s)
      (else (cons-dom (car l) (append-dom (cdr l) s))))))

(define map-sum
  (lambda (f)
    (letrec
      ((loop
         (lambda (dom)
           (cond
             ((null-dom? dom)
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
    (and (null-dom? (cdr dom))
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
      ((null-dom? (cdr dom)) (cdar dom))
      (else (max-dom (cdr dom))))))

(define memv-dom?
  (lambda (v dom)
    (and (value-dom? v)
         (exists (lambda (d) (interval-memq? v d)) dom))))

(define intersection-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null-dom? dom1) (null-dom? dom2)) '())
      ((interval-< (car dom1) (car dom2))
       (intersection-dom (cdr dom1) dom2))
      ((interval-> (car dom1) (car dom2))
       (intersection-dom dom1 (cdr dom2)))
      (else
        (let ((a1 (interval-difference (car dom1) (car dom2)))
              (a2 (interval-difference (car dom2) (car dom1))))
          (append-dom
            (interval-intersection (car dom1) (car dom2))
            (intersection-dom
              (append-dom a1 (cdr dom1))
              (append-dom a2 (cdr dom2)))))))))

(define diff-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null-dom? dom1) (null-dom? dom2)) dom1)
      ((interval-< (car dom1) (car dom2))
       (cons (car dom1) (diff-dom (cdr dom1) dom2)))
      ((interval-> (car dom1) (car dom2))
       (diff-dom dom1 (cdr dom2)))
      (else
        (let ((a1 (interval-difference (car dom1) (car dom2)))
              (a2 (interval-difference (car dom2) (car dom1))))
          (diff-dom
            (append-dom a1 (cdr dom1))
            (append-dom a2 (cdr dom2))))))))

(define copy-before-interval
  (lambda (pred intvl)
    (let ((min (car intvl)) (max (cdr intvl)))
      (let loop ((i min))
        (cond
          ((pred i)
           (if (= min i) `() `((,min . ,(- i 1)))))
          ((= i max) `())
          (else (loop (+ i 1))))))))

(define copy-before-dom
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((let ((intvl (car dom)))
         (and (pred (cdr intvl)) intvl))
       => (lambda (intvl) (copy-before-interval pred intvl)))
      (else (cons (car dom) (copy-before-dom pred (cdr dom)))))))

(define drop-before-interval
  (lambda (pred intvl)
    (let ((min (car intvl)) (max (cdr intvl)))
      (let loop ((i min))
        (cond
          ((pred i) `((,i . ,max)))
          ((= i max) `())
          (else (loop (+ i 1))))))))

(define drop-before-dom
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((let ((intvl (car dom)))
         (and (pred (cdr intvl)) intvl))
       => (lambda (intvl)
            (append (drop-before-interval pred intvl) (cdr dom))))
      (else (drop-before-dom pred (cdr-dom dom))))))

(define disjoint-dom?
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) #t)
      ((interval-< (car dom1) (car dom2))
       (disjoint-dom? (cdr dom1) dom2))
      ((interval-> (car dom1) (car dom2))
       (disjoint-dom? dom1 (cdr dom2)))
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

;; copy-before
(assert (equal?
          (copy-before-dom (lambda (x) (>= x 5)) `((1 . 2) (4 . 6) (8 . 10)))
          `((1 . 2) (4 . 4))))
(assert (equal?
          (copy-before-dom (lambda (x) (<= x 5)) `((1 . 2) (4 . 6) (8 . 10)))
          `()))
(assert (equal?
          (copy-before-dom (lambda (x) (>= x 7)) `((1 . 2) (4 . 6) (8 . 10)))
          `((1 . 2) (4 . 6))))
(assert (equal?
          (copy-before-dom (lambda (x) (>= x 10)) `((1 . 2) (4 . 6) (8 . 10)))
          `((1 . 2) (4 . 6) (8 . 9))))
(assert (equal?
          (copy-before-dom (lambda (x) (>= x 2)) `((1 . 2) (4 . 6) (8 . 10)))
          `((1 . 1))))

;; drop-before
(assert (equal?
          (drop-before-dom (lambda (x) (>= x 5)) `((1 . 2) (4 . 6) (8 . 10)))
          `((5 . 6) (8 . 10))))

(printf "Assertions passed!\n")

