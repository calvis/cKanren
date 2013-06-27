#lang racket

(require (except-in "ck.rkt" walk walk* occurs-check))
(provide
 nom ==-check fresh-nom hash (rename-out [make-tie tie]) unify-s get-sus nom?
 (prefix-out nominal- walk)
 (prefix-out nominal- ==))

(define-var-type nom "a")

(define-syntax-rule (fresh-nom (n ...) g g* ...)
  (fresh-aux nom (n ...) g g* ...))

(define (sus-constrained? x oc)
  (and (eq? (oc-rator oc) 'sus-c)
       (eq? (sus-constraint-v oc) x)))

(define (sus-constraint-v oc) (car (oc-rands oc)))

(define (sus? x)
  (and (pair? x) (eq? (car x) 'sus)))

(define (get-sus x c)
  (let ([ocs (filter/rator 'sus-c c)])
    (let ([oc (findf (lambda (oc) (eq? (sus-constraint-v oc) x)) ocs)])
      (and oc (cons 'sus (oc-rands oc))))))

(define (sus-v s)  (cadr s))
(define (sus-pi s) (caddr s))

(define (sus-c v pi)
  (lambdam@ (a : s c)
    (let ((v (walk v s c)))
      ((update-c (build-oc sus-c v pi)) a))))

(struct tie (a t)
  #:transparent
  #:extra-constructor-name make-tie
  #:methods gen:mk-struct
  [(define (recur tie k)
     (k (tie-a tie) (list (tie-t tie))))
   (define (constructor tie)
     (lambda (a t-ls)
       (make-tie a (car t-ls))))
   (define (override-occurs-check? tie) #f)
   (define (reify-mk-struct tie r)
     (reify-tie tie r))])

(define (reify-tie t r)
  `(tie ,(reify-term (tie-a t) r) 
        ,(reify-term (tie-t t) r)))

(define (sus x pi)
  (sus-c x pi))

(define (== u v)
  (unify-s u v))

(define (unify-s u v)
  (lambdam@ (a : s c)
    (let ((u (walk u s c)) (v (walk v s c)))
      (cond
       ((eq? u v) a)
       ((sus? u)
        (bindm a (update-s (sus-v u) (apply-pi (sus-pi u) v c))))
       ((get-sus u c)
        => (lambda (s)
             (bindm a (update-s u (apply-pi (sus-pi s) v c)))))
       ((sus? v)
        (bindm a (update-s (sus-v v) (apply-pi (sus-pi v) u c))))
       ((get-sus v c)
        => (lambda (s)
             (bindm a (update-s v (apply-pi (sus-pi s) u c)))))
       ((and (tie? u) (tie? v))
        (let ((au (tie-a u)) (av (tie-a v))
              (tu (tie-t u)) (tv (tie-t v)))
          (bindm a
            (if (eq? au av)
                (unify-s tu tv)
                (conj
                 (hash-c au tv)
                 (unify-s tu (apply-pi `((,au . ,av)) tv c)))))))
       ((and (pair? u) (pair? v))
        (bindm a
          (conj
           (unify-s (car u) (car v))
           (unify-s (cdr u) (cdr v)))))
       ((and (var? u) (not (nom? u)))
        (bindm a 
          (conj
           (sus u `())
           (update-s u (apply-pi `() v c)))))
       ((and (var? v) (not (nom? v)))
        (bindm a
          (conj
           (sus v `())
           (update-s v (apply-pi `() u c)))))          
       ((or (nom? u) (nom? v)) mzerom)
       ((equal? u v) a)
       (else mzerom)))))

(define (==-check u v)
  (unify-s-check u v))

(define (unify-s-check u v)
  (lambdam@ (a : s c)
    (let ((u (walk u s c)) (v (walk v s c)))
      (cond
       ((eq? u v) a)
       ((sus? u)
        ((ext-s-check (cadr u) (apply-pi (caddr u) v c)) a))
       ((get-sus u c)
        => (lambda (oc)
             ((ext-s-check u (apply-pi (sus-pi oc) v c)) a)))
       ((sus? v)
        ((ext-s-check (cadr v) (apply-pi (caddr v) u c)) a))
       ((get-sus v c)
        => (lambda (oc)
             ((ext-s-check v (apply-pi (sus-pi oc) u c)) a)))
       ((and (tie? u) (tie? v))
        (let ((au (tie-a u)) (av (tie-a v))
              (tu (tie-t u)) (tv (tie-t v)))
          (if (eq? au av)
              ((unify-s-check tu tv) a)
              ((conj
                (hash-c au tv)
                (unify-s-check tu (apply-pi `((,au . ,av)) tv c)))
               a))))
       ((and (pair? u) (pair? v))
        ((conj
          (unify-s-check (car u) (car v))
          (unify-s-check (cdr u) (cdr v)))
         a))
       ((and (var? u) (not (nom? u)))
        ((conj
          (sus u `())
          (ext-s-check u (apply-pi `() v c)))
         a))
       ((and (var? v) (not (nom? v)))
        ((conj
          (sus v `())
          (ext-s-check v (apply-pi `() u c)))
         a))          
       ((or (nom? u) (nom? v)) mzerom)
       ((equal? u v) a)
       (else mzerom)))))

(define (ext-s-check x u)
  (lambdam@ (a : s c)
    (cond
     [(occurs-check x u s c)
      ((update-s x u) a)]
     [else mzerom])))

(define (occurs-check x t s c)
  (let rec ([t t])
    (let ([t (walk (tie-t* t) s c)])
      (cond
       [(sus? t) (not (eq? x (sus-v t)))]
       [(get-sus t c)
        => (lambda (sus-c)
             (not (eq? x (sus-v sus-c))))]
       [(pair? t) (and (rec (car t)) (rec (cdr t)))]
       [else #t]))))

(define (hash b t)
  (hash-c b t))

(define (hash-c b t)
  (let rec ((t t))
    (lambdam@ (a : s c)
      (let ((t (walk t s c)))
        (cond
         ((eq? b t) mzerom)
         ((sus? t)
          (let ((lhs (apply-pi (caddr t) b c)))
            ((update-c (build-oc hash-c lhs t)) a)))
         ((get-sus t c)
          => (lambda (sus-c)
               (let ((lhs (apply-pi (sus-pi sus-c) b c)))
                 ((update-c (build-oc hash-c lhs t)) a))))
         ((tie? t)
          (if (eq? b (tie-a t)) a ((rec (tie-t t)) a)))
         ((pair? t)
          ((conj (rec (car t)) (rec (cdr t))) a))
         ((and (var? t) (not (nom? t)))
          ((conj (sus t `()) (rec t)) a))
         (else a))))))

(define (tie-t* t)
  (if (tie? t) (tie-t* (tie-t t)) t))

(define (walk x s c)
  (let f ((x x) (pi '()))
    (cond
     ((sus? x)
      (cond
       ((assq (sus-v x) s)
        => (lambda (a) (f (cdr a) (compose-pis (sus-pi x) pi))))
       (else (apply-pi pi x c))))
     ((get-sus x c)
      => (lambda (sus-c)
           (cond
            ((assq x s)
             => (lambda (a)
                  (f (cdr a) 
                     (compose-pis (sus-pi sus-c) pi))))
            (else (apply-pi pi x c)))))
     (else (apply-pi pi x c)))))

(define (walk* t s c)
  (let ((t (walk t s c)))
    (cond
     ((tie? t)
      (make-tie (tie-a t) (walk* (tie-t t) s c)))
     ((pair? t)
      (cons (walk* (car t) s c) (walk* (cdr t) s c)))
     (else t))))

(define compose-pis append)

(define (get-noms pi s)
  (define (with n s) (if (memq n s) s (cons n s)))
  (cond
   ((null? pi) s)
   (else (get-noms (cdr pi) (with (caar pi) (with (cdar pi) s))))))

(define (pi-ds pi1 pi2 c)
  (for/fold ([s '()])
            ([nom (get-noms pi1 (get-noms pi2 '()))])
    (cond
     ((eq? (apply-pi pi1 nom c) (apply-pi pi2 nom c)) s)
     (else (cons nom s)))))

(define (id-pi? pi c) (null? (pi-ds pi '() c)))

(define (app pi a)
  (let ((pi (reverse pi)))
    (cond
     ((null? pi) a)
     ((eq? (caar pi) a)
      (app (cdr pi) (cdar pi)))
     ((eq? (cdar pi) a)
      (app (cdr pi) (caar pi)))
     (else (app (cdr pi) a)))))

(define (apply-pi pi t c)
  (let rec ((t t))
    (cond
     ((nom? t) (app pi t))
     ((sus? t)
      (let ((pi (compose-pis pi (caddr t))))
        (if (id-pi? pi c) t `(sus ,(cadr t) ,pi))))
     ((get-sus t c)
      => (lambda (sus-c)
           (let ((pi (compose-pis pi (sus-pi sus-c))))
             (if (id-pi? pi c) t `(sus ,t ,pi)))))
     ((var? t)
      (if (id-pi? pi c) t `(sus ,t ,pi)))
     ((tie? t) 
      (make-tie (app pi (tie-a t))
                (rec (tie-t t))))
     ((pair? t) (cons (rec (car t)) (rec (cdr t))))
     (else t))))

(define (reify-alpha-constraints v r c)
  (let ((c (filter-memq/rator '(sus-c hash-c) c)))
    (let ((c (reify-alpha r c)))
      (if (null? c) c `((alpha . ,c))))))

(define (reify-alpha r c)
  (for/fold ([c^ '()])
            ([oc c])
    (cond
     ((reify-oc oc r)
      => (lambda (oc-sym)
           (if (member oc-sym c^) c^ (cons oc-sym c^))))
     (else c^))))

(define (reify-oc oc r)
  (case (oc-rator oc)
    ((hash-c)
     (let ((lhs (car (oc-rands oc)))
           (rhs (cadr (oc-rands oc))))
       (let ((rhs (if (sus? rhs) (cadr rhs) rhs)))
         (let ((lhs (reify-cvar lhs r))
               (rhs (reify-cvar rhs r)))
           (and (not (any/var? lhs))
                (not (any/var? rhs))
                `(hash (,lhs ,rhs)))))))
    (else #f)))

(extend-reify-fns 'alpha reify-alpha-constraints)

