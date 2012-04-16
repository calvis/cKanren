(library
  (cKanren fd)
  (export
    infd domfd =fd =/=fd <=fd <fd
    plusfd timesfd distinctfd range)
  (import
    (rename (rnrs) (list-sort rnrs:list-sort))
    (cKanren ck)
    (cKanren interval-domain))

;;; helpers

(define list-sort rnrs:list-sort)

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

(define get-dom
  (lambda (x c)
    (cond
      ((find (pred_x x) c)
       => (lambda (oc) (cadr (oc->rands oc))))
      (else #f))))

(define process-dom
  (lambda (v dom)
    (lambdam@ (a)
      (cond
        ((var? v) ((update-var-dom v dom) a))
        ((memv-dom? v dom) a)
        (else #f)))))

(define update-var-dom 
  (lambda (x dom)
    (lambdam@ (a : s c)
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
    (lambdam@ (a : s c)
      (cond
        ((singleton-dom? dom)
         (let ((n (singleton-element-dom dom)))
           ((update-s x n) a)))
        (else (make-a s (ext-d x dom c)))))))

(define force-ans
  (lambda (x)
    (lambdag@ (a : s c)
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
    (lambdam@ (a : s c)
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
    (lambdam@ (a : s c)
      (let ((v* (walk* v* s)))
        (cond
          ((not (list? v*))
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
    (lambdam@ (a : s c)
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
                ((var? y)
                 (loop (cdr y*) n* (cons y x*)))
                ;; n* is NOT A DOM
                ((memv y n*) #f)
                (else
                  (let ((n* (list-insert < y n*)))
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
     (lambdam@ (a : s c)
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
            (copy-before-dom (lambda (u) (< vmax u)) d_u))
          (process-dom v
            (drop-before-dom (lambda (v) (<= umin v)) d_v)))))))

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

(define timesfd-c
  (lambda (u v w)
    (let ((safe-div (lambda (n c a) (if (zero? n) c (div a n)))))
      (c-op timesfd-c ((u : d_u) (v : d_v) (w : d_w))
        (let ((wmin (min-dom d_w)) (wmax (max-dom d_w))
              (umin (min-dom d_u)) (umax (max-dom d_u))
              (vmin (min-dom d_v)) (vmax (max-dom d_v)))
          (let ([u-range (range
                           (safe-div vmax umin wmin)
                           (safe-div vmin umax wmax))]
                [v-range (range
                           (safe-div umax vmin wmin)
                           (safe-div umin vmax wmax))]
                [w-range (range (* umin vmin) (* umax vmax))])
            (composem
              (process-dom w w-range)
              (composem
                (process-dom u u-range)
                (process-dom v v-range)))))))))

(define enforce-constraintsfd
  (lambda (x)
    (fresh ()
      (force-ans x)
      (lambdag@ (a : s c)
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
      (let ((oc (car c)))
        (if (memq (oc->rator oc)
              '(=/=fd-c distinctfd-c distinct/fd-c
                <=fd-c =fd-c plusfd-c timesfd-c))
            (cond
              ((find (lambda (x) (not (memq x bound-x*)))
                 (filter var? (oc->rands oc)))
               => (lambda (x)
                    (unless (value-dom? (walk x s))
                      (error 'verify-all-bound
                        "Constrained variable ~s without domain" x))))))
        (verify-all-bound s (cdr c) bound-x*)))))

;;; goals

(define domfd
  (lambda (x n*)
    (goal-construct (domfd-c x n*))))

(define domfd-c
  (lambda (x n*)
    (lambdam@ (a : s c)
      ((process-dom (walk x s) (make-dom n*)) a))))

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

(define timesfd
  (lambda (u v w)
    (goal-construct (timesfd-c u v w))))

(define distinctfd
  (lambda (v*)
    (goal-construct (distinctfd-c v*))))

(extend-enforce-fns 'fd enforce-constraintsfd)

)

