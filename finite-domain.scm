(library
  (finite-domain)
  (export range value-dom? list-sorted? list-insert
    map-sum null-dom? singleton-dom? singleton-element-dom
    min-dom max-dom memv-dom? intersection-dom diff-dom
    copy-before drop-before disjoint-dom? make-dom)
  (import (rnrs) (ck))

;;; domains (sorted lists of integers)

(define range
  (lambda (lb ub)
    (cond
      ((< lb ub) (cons lb (range (+ lb 1) ub)))
      (else (cons lb '())))))

(define value-dom?
  (lambda (v)
    (and (integer? v) (<= 0 v))))

;; n* should be a non-empty sorted (small to large) list
;; of value-doms?, with no duplicates.
(define make-dom (lambda (n*) n*))

(define map-sum
  (lambda (f)
    (letrec
      ((loop
         (lambda (ls)
           (cond
             ((null? ls)
              (lambdag@ (a) (mzerog)))
             (else
               (conde
                 ((f (car ls)))
                 ((loop (cdr ls)))))))))
      loop)))

(define null-dom?
  (lambda (x)
    (null? x)))

(define singleton-dom?
  (lambda (dom)
    (null? (cdr dom))))

(define singleton-element-dom
  (lambda (dom)
    (car dom)))

(define min-dom
  (lambda (dom)
    (car dom)))

(define max-dom
  (lambda (dom)
    (cond
      ((null? (cdr dom)) (car dom))
      (else (max-dom (cdr dom))))))

(define memv-dom?
  (lambda (v dom)
    (and (value-dom? v) (memv v dom))))

(define intersection-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) '())
      ((= (car dom1) (car dom2))
       (cons (car dom1)
         (intersection-dom (cdr dom1) (cdr dom2))))
      ((< (car dom1) (car dom2))
       (intersection-dom (cdr dom1) dom2))
      (else (intersection-dom dom1 (cdr dom2))))))

(define diff-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) dom1)
      ((= (car dom1) (car dom2))
       (diff-dom (cdr dom1) (cdr dom2)))
      ((< (car dom1) (car dom2))
       (cons (car dom1) (diff-dom (cdr dom1) dom2)))
      (else (diff-dom dom1 (cdr dom2))))))

(define copy-before   
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((pred (car dom)) '())
      (else (cons (car dom) (copy-before pred (cdr dom)))))))

(define drop-before
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((pred (car dom)) dom)
      (else (drop-before pred (cdr dom))))))

(define disjoint-dom?
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) #t)
      ((= (car dom1) (car dom2)) #f)
      ((< (car dom1) (car dom2))
       (disjoint-dom? (cdr dom1) dom2))
      (else (disjoint-dom? dom1 (cdr dom2))))))

)


