#lang racket

(require "interval-domain.rkt" "ck.rkt")

(provide infd domfd =fd =/=fd <=fd <fd
         plusfd timesfd distinctfd range
         force-ans)

;;; goals

(define (domfd x n*)
  (domfd-c x n*))

(define (domfd-c x n*)
  (lambdam@ (a : s c)
    ((process-dom (walk x s) (make-dom n*)) a)))

(define-syntax-rule (infd x0 x ... e)
  (let ((n* e))
    (conj (domfd x0 n*) (domfd x n*) ...)))

(define (=fd u v)
  (=fd-c u v))

(define (=/=fd u v)
  (=/=fd-c u v))

(define (<fd u v)
  (conj (<=fd u v) (=/=fd u v)))

(define (<=fd u v)
  (<=fd-c u v))

(define (plusfd u v w)
  (plusfd-c u v w))

(define (timesfd u v w)
  (timesfd-c u v w))

(define (distinctfd v*)
  (distinctfd-c v*))

;;; 

(define ((existing-domain x) oc)
  (eq? (car (oc-rands oc)) x))

;; gives x the domain dom in the constraint store c
(define (ext-d x dom)
  (lambdam@ (a : s c)
    (let ([oc (build-oc domfd-c x dom)]
          [ocs (filter/rator 'domfd-c c)]
          [pred (existing-domain x)])
      (let-values ([(x-doms other-doms)
                    (partition (existing-domain x) ocs)])
        (cond
         ((null? x-doms) ((update-c oc) a))
         (else ((replace-ocs 'domfd-c (append (list oc) other-doms)) a)))))))

(define get-dom
  (lambda (x c)
    (let ([domocs (filter/rator 'domfd-c c)])
      (cond
       ((findf (existing-domain x) domocs)
        => (lambda (oc) (cadr (oc-rands oc))))
       (else #f)))))

(define process-dom
  (lambda (v dom)
    (lambdam@ (a)
      (cond
        ((var? v) ((update-var-dom v dom) a))
        ((memv-dom? v dom) a)
        (else mzerom)))))

(define update-var-dom 
  (lambda (x dom)
    (lambdam@ (a : s c)
      (cond
        ((get-dom x c)
         => (lambda (xdom)
              (let ((i (intersection-dom xdom dom)))
                (cond
                  ((null-dom? i) mzerom)
                  (else ((resolve-storable-dom i x) a))))))
        (else ((resolve-storable-dom dom x) a))))))

(define resolve-storable-dom
  (lambda (dom x)
    (lambdam@ (a : s c)
      (cond
       [(singleton-dom? dom)
        (let ([n (singleton-element-dom dom)])
          ((update-s x n) a))]
       [else ((ext-d x dom) a)]))))

(define (force-ans x)
  (lambdam@ (a : s c)
    (let ([x (walk x s)])
      (bindm a
        (cond
         [(and (var? x) (get-dom x c))
          => (map-sum 
              (lambda (v) 
                (update-s x v)))]
         [(pair? x)
          (conj
           (force-ans (car x))
           (force-ans (cdr x)))]
         [else identitym])))))

(define-syntax let-dom
  (syntax-rules (:)
    ((_ (s c) ([u : d_u] ...) body)
     (let ([u (walk u s)] ...)
       (let ([d_u
              (cond
               ((var? u) (get-dom u c))
               (else (make-dom `(,u))))]
             ...)
         body)))))

(define (=/=fd-c u v)
  (lambdam@ (a : s c)
    (let-dom (s c) ((u : d_u) (v : d_v))
      (cond
       ((or (not d_u) (not d_v))
        ((update-c (build-oc =/=fd-c u v)) a))
       ((and (singleton-dom? d_u)
             (singleton-dom? d_v)
             (= (singleton-element-dom d_u)
                (singleton-element-dom d_v)))
        mzerom)
       ((disjoint-dom? d_u d_v) a)
       (else
        (let ((oc (build-oc =/=fd-c u v)))
          (bindm a
           (conj
            (update-c oc)
            (cond
             [(singleton-dom? d_u)
              (process-dom v (diff-dom d_v d_u))]
             [(singleton-dom? d_v)
              (process-dom u (diff-dom d_u d_v))]
             [else identitym])))))))))

(define (distinctfd-c v*)
  (lambdam@ (a : s c)
    (let ([v* (walk* v* s)])
      (cond
       ((not (list? v*))
        (let ((oc (build-oc distinctfd-c v*)))
          ((update-c oc) a))) 
       (else
        (let-values (((x* n*) (partition var? v*)))
          (let ((n* (sort n* <)))
            (cond
             ((list-sorted? < n*)
              ((distinct/fd-c x* n*) a))
             (else mzerom)))))))))

(define (distinct/fd-c y* n*)
  (lambdam@ (a : s c)
    (let loop ([y* y*] [n* n*] [x* '()])
      (cond
       ((null? y*)
        (let* ((oc (build-oc distinct/fd-c x* n*)))
          ((conj
            (update-c oc)
            (exclude-from-dom (make-dom n*) c x*))
           a)))
       (else
        (let ((y (walk (car y*) s)))
          (cond
           ((var? y)
            (loop (cdr y*) n* (cons y x*)))
           ;; n* is NOT A DOM
           ((memv y n*) mzerom)
           (else
            (let ((n* (list-insert < y n*)))
              (loop (cdr y*) n* x*))))))))))

(define (exclude-from-dom dom1 c x*)
  (for/fold ([fn identitym])
            ([x x*])
    (cond
     [(get-dom x c)
      => (lambda (dom2)
           (conj
            (process-dom x (diff-dom dom2 dom1))
            fn))]
     [else fn])))

(define-syntax c-op  
  (syntax-rules (:)
    ((_ op ([u : d_u] ...) body)
     (lambdam@ (a : s c)
       (let-dom (s c) ([u : d_u] ...)
         (let ([oc (build-oc op u ...)])
           ((conj
             (update-c oc)
             (cond
              [(and d_u ...) body]
              [else identitym]))
            a)))))))

(define (=fd-c u v)
  (c-op =fd-c ([u : d_u] [v : d_v])
    (let ([i (intersection-dom d_u d_v)])
      (conj
       (process-dom u i)
       (process-dom v i)))))

(define (<=fd-c u v)
  (c-op <=fd-c ([u : d_u] [v : d_v])
    (let ([umin (min-dom d_u)]
          [vmax (max-dom d_v)])
      (let ([new-u-dom (copy-before-dom (lambda (u) (< vmax u)) d_u)]
            [new-v-dom (drop-before-dom (lambda (v) (<= umin v)) d_v)])
        (conj
         (process-dom u new-u-dom)
         (process-dom v new-v-dom))))))

(define (plusfd-c u v w)
  (c-op plusfd-c ([u : d_u] [v : d_v] [w : d_w])
    (let ([wmin (min-dom d_w)] [wmax (max-dom d_w)]
          [umin (min-dom d_u)] [umax (max-dom d_u)]
          [vmin (min-dom d_v)] [vmax (max-dom d_v)])
      (let ([new-w-dom (range (+ umin vmin) (+ umax vmax))]
            [new-u-dom (range (- wmin vmax) (- wmax vmin))]
            [new-v-dom (range (- wmin umax) (- wmax umin))])
        (conj
         (process-dom w new-w-dom)
         (process-dom u new-u-dom)
         (process-dom v new-v-dom))))))

(define (timesfd-c u v w)
  (let ((safe-div (lambda (n c a) (if (zero? n) c (quotient a n)))))
    (c-op timesfd-c ([u : d_u] [v : d_v] [w : d_w])
      (let ([wmin (min-dom d_w)] [wmax (max-dom d_w)]
            [umin (min-dom d_u)] [umax (max-dom d_u)]
            [vmin (min-dom d_v)] [vmax (max-dom d_v)])
        (let ([new-w-dom 
               (range (* umin vmin) (* umax vmax))]
              [new-u-dom
               (range
                (safe-div vmax umin wmin)
                (safe-div vmin umax wmax))]
              [new-v-dom 
               (range
                (safe-div umax vmin wmin)
                (safe-div umin vmax wmax))])
          (conj
           (process-dom w new-w-dom)
           (process-dom u new-u-dom)
           (process-dom v new-v-dom)))))))

(define (enforce-constraintsfd x)
  (define (domfd-c->var domfd-c) 
    (car (oc-rands domfd-c)))
  (conj
    (force-ans x)
    (lambdam@ (a : s c)
      (let ([domains (filter/rator 'domfd-c c)])
        (let ([bound-x* (map domfd-c->var domains)])
          (verify-all-bound s c bound-x*)
          ((conj
             (onceo (force-ans bound-x*))
             (lambdam@ (a^) a)) 
           a))))))

(define fd-cs '(=/=fd-c distinctfd-c distinct/fd-c 
                <=fd-c =fd-c plusfd-c timesfd-c))
(define (fd-c? oc) (memq (oc-rator oc) fd-cs))

(define (verify-all-bound s c bound-x*)
  (define (bound? x) (memq x bound-x*))
  (for ([oc (c->list c)] #:when (fd-c? oc))
    (define oc-vars (filter var? (oc-rands oc)))
    (cond
     ((findf (compose not bound?) oc-vars)
      => (lambda (x)
           (unless (value-dom? (walk x s))
             (error 'verify-all-bound
                    "constrained variable ~s without domain" x)))))))

;;; helpers

(define (list-sorted? pred ls)
  (cond
   ((or (null? ls) (null? (cdr ls))) #t)
   ((pred (car ls) (cadr ls))
    (list-sorted? pred (cdr ls)))
   (else #f)))

(define (list-insert pred x ls)
  (cond
   ((null? ls) (cons x '()))
   ((pred x (car ls)) (cons x ls))
   (else (cons (car ls) (list-insert pred x (cdr ls))))))

;;; 

(extend-enforce-fns 'fd enforce-constraintsfd)

