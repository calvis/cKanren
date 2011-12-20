(library
  (fd)
  (export
    infd domfd =fd =/=fd <=fd <fd
    plusfd distinctfd range)
  (import (rnrs) (ck))

;;; helpers

(define range
  (lambda (lb ub)
    (cond
      ((< lb ub) (cons lb (range (+ lb 1) ub)))
      (else (cons lb '())))))

(define-syntax lambdamfd@
  (syntax-rules ()
    ((_ (a) e) (lambdam@ (a) e))
    ((_ (a : s c) e) (lambdam@ (a : s c) e))))

(define-syntax lambdagfd@
  (syntax-rules ()
    ((_ (a) e) (lambdag@ (a) e))
    ((_ (a : s c) e) (lambdag@ (a : s c) e))))

(define pred_x
  (lambda (x)
    (lambda (oc)
      (and (eq? (oc->rator oc) 'domfd-c)
           (eq? (car (oc->rands oc)) x)))))

(define ext-d
  (lambda (x dom c)
    (let ((oc (build-oc domfd-c x dom)))
      (let ((pred (pred_x x)))
        (cond
          ((find pred c) (cons oc (remp pred c)))
          (else (cons oc c)))))))

;;; domains (sorted lists of integers)

(define value-dom?
  (lambda (v)
    (and (integer? v) (<= 0 v))))

;; n* should be a non-empty sorted (small to large) list
;; of value-doms?, with no duplicates.
(define make-dom (lambda (n*) n*))

(define list-sorted?
  (lambda (pred ls)
    (cond
      ((or (null? ls) (null? (cdr ls))) #t)
      ((pred (car ls) (cadr ls))
       (list-sorted? pred (cdr ls)))
      (else #f))))

(define list-insert
  (lambda (pred x ls)
    (cond
      ((null? ls) (cons x '()))
      ((pred x (car ls)) (cons x ls))
      (else (cons (car ls) (list-insert pred x (cdr ls)))))))
  
(define map-sum
  (lambda (f)
    (letrec
      ((loop
         (lambda (ls)
           (cond
             ((null? ls) (lambdagfd@ (a) (mzerog)))
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

;;; procedures below this point cannot
;;; expose the representations of doms!

;; (define get-dom
;;   (lambda (x c)
;;     (cond
;;       ((find (lambda (oc) (and (eq? (oc->rator oc) 'domfd-c)
;;                           (eq? (car (oc->rands oc)) x))) c)
;;        => (lambda (oc) (cadr (oc->rands oc))))
;;       (else #f))))

(define get-dom
  (lambda (x c)
    (cond
      ((find (pred_x x) c)
       => (lambda (oc) (cadr (oc->rands oc))))
      (else #f))))

(define process-dom
  (lambda (v dom)
    (lambdamfd@ (a)
      (cond
        ((var? v) ((update-var-dom v dom) a))
        ((memv-dom? v dom) a)
        (else #f)))))

(define update-var-dom 
  (lambda (x dom)
    (lambdamfd@ (a : s c)
      (cond
        ((get-dom x c)
         => (lambda (xdom)
              (let ((i (intersection-dom xdom dom)))
                (cond
                  ((null-dom? i) #f)
                  (else ((resolve-storable-dom i x) a))))))
        (else ((resolve-storable-dom dom x) a))))))

(define resolve-storable-dom
  (lambda (dom x)
    (lambdamfd@ (a : s c)
      (cond
        ((singleton-dom? dom)
         (let ((n (singleton-element-dom dom)))
           ((update-s x n) a)))
        (else (make-a s (ext-d x dom c)))))))

(define force-ans
  (lambda (x)
    (lambdagfd@ (a : s c)
      (let ((x (walk x s)))
        ((cond
           ((and (var? x) (get-dom x c))
            => (map-sum (lambda (v) (update-s x v))))
           ((pair? x)
            (fresh ()
              (force-ans (car x))
              (force-ans (cdr x))))
           (else (lambdag@ (a) (unitg a))))
         a)))))

(define-syntax let-dom
  (syntax-rules (:)
    ((_ (s c) ((u : d_u) ...) body)
     (let ((u (walk u s)) ...)
       (let ((d_u
               (cond
                 ((var? u) (get-dom u c))
                 (else (make-dom `(,u)))))
             ...)
         body)))))

(define =/=fd-c
  (lambda (u v)
    (lambdamfd@ (a : s c)
      (let-dom (s c) ((u : d_u) (v : d_v))
        (cond
          ((or (not d_u) (not d_v))
           ((update-c (build-oc =/=fd-c u v)) a))
          ((and (singleton-dom? d_u)
                (singleton-dom? d_v)
                (= (singleton-element-dom d_u)
                   (singleton-element-dom d_v)))
           #f)
          ((disjoint-dom? d_u d_v) a)
          (else
            (let ((oc (build-oc =/=fd-c u v)))
              (cond
                ((singleton-dom? d_u)
                 ((composem
                    (update-c oc)
                    (process-dom v (diff-dom d_v d_u)))
                  a))
                ((singleton-dom? d_v)
                 ((composem
                    (update-c oc)
                    (process-dom u (diff-dom d_u d_v)))
                  a))
                (else ((update-c oc) a))))))))))

(define distinctfd-c
  (lambda (v*)
    (lambdamfd@ (a : s c)
      (let ((v* (walk v* s)))
        (cond
          ((var? v*)
           (let ((oc (build-oc distinctfd-c v*)))
             ((update-c oc) a))) 
          (else
            (let-values (((x* n*) (partition var? v*)))
              (let ((n* (list-sort < n*)))
                (cond
                  ((list-sorted? < n*)
                   ((distinct/fd-c x* n*) a))
                  (else #f))))))))))

(define distinct/fd-c
  (lambda (y* n*)
    (lambdamfd@ (a : s c)
      (let loop ((y* y*) (n* n*) (x* '()))
        (cond
          ((null? y*)
           (let* ((oc (build-oc distinct/fd-c x* n*)))
             ((composem
                (update-c oc)
                (exclude-from-dom (make-dom n*) c x*))
              a)))
          (else
            (let ((y (walk (car y*) s)))
              (cond
                ((var? y) (loop (cdr y*) n* (cons y x*)))
                ((memv-dom? y n*) #f)
                (else (let ((n* (list-insert < y n*)))
                        (loop (cdr y*) n* x*)))))))))))

(define exclude-from-dom
  (lambda (dom1 c x*)
    (let loop ((x* x*))
      (cond
        ((null? x*) identitym)
        ((get-dom (car x*) c)
         => (lambda (dom2)
              (composem
                (process-dom (car x*) (diff-dom dom2 dom1))
                (loop (cdr x*)))))
        (else (loop (cdr x*)))))))

(define-syntax c-op  ;;; returns sequel.
  (syntax-rules (:)
    ((_ op ((u : d_u) ...) body)
     (lambdamfd@ (a : s c)
       (let-dom (s c) ((u : d_u) ...)
         (let* ((oc (build-oc op u ...)))
           (cond
             ((and d_u ...) ((composem (update-c oc) body) a))
             (else ((update-c oc) a)))))))))

(define =fd-c
  (lambda (u v)
    (c-op =fd ((u : d_u) (v : d_v))
      (let ((i (intersection-dom d_u d_v)))
        (composem
          (process-dom u i)
          (process-dom v i))))))

(define <=fd-c
  (lambda (u v)
    (c-op <=fd-c ((u : d_u) (v : d_v))
      (let ((umin (min-dom d_u))
            (vmax (max-dom d_v)))
        (composem
          (process-dom u
            (copy-before (lambda (u) (< vmax u)) d_u))
          (process-dom v
            (drop-before (lambda (v) (<= umin v)) d_v)))))))

(define plusfd-c
  (lambda (u v w)
    (c-op plusfd-c ((u : d_u) (v : d_v) (w : d_w))
      (let ((wmin (min-dom d_w)) (wmax (max-dom d_w))
            (umin (min-dom d_u)) (umax (max-dom d_u))
            (vmin (min-dom d_v)) (vmax (max-dom d_v)))
        (composem
          (process-dom w
            (range (+ umin vmin) (+ umax vmax)))
          (composem
            (process-dom u
              (range (- wmin vmax) (- wmax vmin)))
            (process-dom v
              (range (- wmin umax) (- wmax umin)))))))))

(define enforce-constraintsfd
  (lambda (x)
    (fresh ()
      (force-ans x)
      (lambdagfd@ (a : s c)
        (let ((bound-x* (map
                          (lambda (oc)
                            (let ((r (oc->rands oc)))
                              (car r)))
                          (filter
                            (lambda (oc) (eq? (oc->rator oc) 'domfd-c))
                            c))))
          (verify-all-bound s c bound-x*)
          ((onceo (force-ans bound-x*)) a))))))

(define verify-all-bound
  (lambda (s c bound-x*)
    (unless (null? c)
      (cond
        ((find (lambda (x) (not (memq x bound-x*)))
           (filter var? (oc->rands (car c))))
         => (lambda (x)
              (unless (value-dom? (walk x s))
                (error 'verify-all-bound
                  "Constrained variable ~s without domain" x))))
        (else (verify-all-bound s (cdr c) bound-x*))))))

;;; goals

(define domfd
  (lambda (x n*)
    (goal-construct (domfd-c x n*))))

(define domfd-c
  (lambda (x n*)
    (lambdamfd@ (a : s c)
      ((process-dom (walk x s) (make-dom (list-sort < n*))) a))))

(define-syntax infd
  (syntax-rules ()
    ((_ x0 x ... e)
     (let ((n* e))
       (fresh () (domfd x0 n*) (domfd x n*) ...)))))

(define =fd
  (lambda (u v)
    (goal-construct (=fd-c u v))))

(define =/=fd
  (lambda (u v)
    (goal-construct (=/=fd-c u v))))

(define <fd
  (lambda (u v)
    (fresh () (<=fd u v) (=/=fd u v))))

(define <=fd
  (lambda (u v)
    (goal-construct (<=fd-c u v))))

(define plusfd
  (lambda (u v w)
    (goal-construct (plusfd-c u v w))))

(define distinctfd
  (lambda (v*)
    (goal-construct (distinctfd-c v*))))

(extend-enforce-fns 'fd enforce-constraintsfd)

)

(import (fd))

