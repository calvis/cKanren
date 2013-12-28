#lang racket

(require (except-in cKanren/ck walk walk* occurs-check)
         cKanren/src/constraints
         cKanren/src/framework
         (rename-in cKanren/src/events [findf e:findf]))
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

(define (get-sus x c e)
  (or (let ([rands* (filter/rator sus-c c)])
        (let ([rands (findf (match-lambda [(list v pi) (eq? v x)] [else #f]) rands*)])
          (and rands (cons 'sus rands))))
      (e:findf (match-lambda 
                 [(add-constraint-event/internal rator (list v pi))
                  (and (eq? sus-c rator)
                       (eq? v x))]
                 [else #f])
               e)))

(define (sus-v s)  (cadr s))
(define (sus-pi s) (caddr s))

(define-constraint (sus-c v [pi #:constant])
  (add-constraint (sus-c v pi)))

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

(define-constraint (unify-s u v)
  #:package (a [s c e])
  (cond
   ((eq? u v) succeed)
   ((sus? u)
    (add-association (sus-v u) (apply-pi (sus-pi u) v c e)))
   ((get-sus u c e)
    => (lambda (s)
         (add-association u (apply-pi (sus-pi s) v c e))))
   ((sus? v)
    (add-association (sus-v v) (apply-pi (sus-pi v) u c e)))
   ((get-sus v c e)
    => (lambda (s)
         (add-association v (apply-pi (sus-pi s) u c e))))
   ((and (tie? u) (tie? v))
    (let ((au (tie-a u)) (av (tie-a v))
          (tu (tie-t u)) (tv (tie-t v)))
      (if (eq? au av)
          (unify-s tu tv)
          (conj
           (hash au tv)
           (unify-s tu (apply-pi `((,au . ,av)) tv c e))))))
   ((and (pair? u) (pair? v))
    (conj
     (unify-s (car u) (car v))
     (unify-s (cdr u) (cdr v))))
   ((and (var? u) (not (nom? u)))
    (conj
     (sus u `())
     (add-association u (apply-pi `() v c e))))
   ((and (var? v) (not (nom? v)))
    (conj
     (sus v `())
     (add-association v (apply-pi `() u c e))))
   ((or (nom? u) (nom? v)) fail)
   ((equal? u v) succeed)
   (else fail)))

(define (==-check u v)
  (unify-s-check u v))

(define-constraint (unify-s-check u v)
  #:package (a [s c e])
  (cond
   ((eq? u v) succeed)
   ((sus? u)
    (ext-s-check (cadr u) (apply-pi (caddr u) v c e)))
   ((get-sus u c e)
    => (lambda (oc)
         (ext-s-check u (apply-pi (sus-pi oc) v c e))))
   ((sus? v)
    (ext-s-check (cadr v) (apply-pi (caddr v) u c e)))
   ((get-sus v c e)
    => (lambda (oc)
         (ext-s-check v (apply-pi (sus-pi oc) u c e))))
   ((and (tie? u) (tie? v))
    (let ((au (tie-a u)) (av (tie-a v))
          (tu (tie-t u)) (tv (tie-t v)))
      (if (eq? au av)
          (unify-s-check tu tv)
          (conj
           (hash au tv)
           (unify-s-check tu (apply-pi `((,au . ,av)) tv c e))))))
   ((and (pair? u) (pair? v))
    (conj
     (unify-s-check (car u) (car v))
     (unify-s-check (cdr u) (cdr v))))
   ((and (var? u) (not (nom? u)))
    (conj
     (sus u `())
     (ext-s-check u (apply-pi `() v c e))))
   ((and (var? v) (not (nom? v)))
    (conj
     (sus v `())
     (ext-s-check v (apply-pi `() u c e))))
   ((or (nom? u) (nom? v)) fail)
   ((equal? u v) succeed)
   (else fail)))

(define (ext-s-check x u)
  (transformer
   #:package (a [s c e])
   (cond
    [(occurs-check x u s c e)
     (add-association x u)]
    [else fail])))

(define (occurs-check x t s c e)
  (let rec ([t t])
    (let ([t (walk (tie-t* t) s c e)])
      (cond
       [(sus? t) (not (eq? x (sus-v t)))]
       [(get-sus t c e)
        => (lambda (sus-c)
             (not (eq? x (sus-v sus-c))))]
       [(pair? t) (and (rec (car t)) (rec (cdr t)))]
       [else #t]))))

(define-constraint (hash b t)
  #:package (a [s c e])
  #:reification-function
  (lambda (ans r)
    (let ((lhs b)
          (rhs t))
      (let ((rhs (if (sus? rhs) (cadr rhs) rhs)))
        `(hash (,lhs ,rhs)))))
  (let rec ((t t))
    (let ((t (walk t s c e)))
      (cond
       ((eq? b t) fail)
       ((sus? t)
        (let ((lhs (apply-pi (caddr t) b c e)))
          (add-constraint (hash lhs t))))
       ((get-sus t c e)
        => (lambda (sus-c)
             (let ((lhs (apply-pi (sus-pi sus-c) b c e)))
               (add-constraint (hash lhs t)))))
       ((tie? t)
        (if (eq? b (tie-a t)) succeed (rec (tie-t t))))
       ((pair? t)
        (conj (rec (car t)) (rec (cdr t))))
       ((and (var? t) (not (nom? t)))
        (conj (sus t `()) (rec t)))
       (else succeed)))))

(define (tie-t* t)
  (if (tie? t) (tie-t* (tie-t t)) t))

(define (walk x s c e)
  (let f ((x x) (pi '()))
    (cond
     ((sus? x)
      (cond
       ((assq (sus-v x) s)
        => (lambda (a) (f (cdr a) (compose-pis (sus-pi x) pi))))
       (else (apply-pi pi x c e))))
     ((get-sus x c e)
      => (lambda (sus-c)
           (cond
            ((assq x s)
             => (lambda (a)
                  (f (cdr a) 
                     (compose-pis (sus-pi sus-c) pi))))
            (else (apply-pi pi x c e)))))
     (else (apply-pi pi x c e)))))

(define compose-pis append)

(define (get-noms pi s)
  (define (with n s) (if (memq n s) s (cons n s)))
  (cond
   ((null? pi) s)
   (else (get-noms (cdr pi) (with (caar pi) (with (cdar pi) s))))))

(define (pi-ds pi1 pi2 c e)
  (for/fold ([s '()])
            ([nom (get-noms pi1 (get-noms pi2 '()))])
    (cond
     ((eq? (apply-pi pi1 nom c e) (apply-pi pi2 nom c e)) s)
     (else (cons nom s)))))

(define (id-pi? pi c e) (null? (pi-ds pi '() c e)))

(define (app pi a)
  (let ((pi (reverse pi)))
    (cond
     ((null? pi) a)
     ((eq? (caar pi) a)
      (app (cdr pi) (cdar pi)))
     ((eq? (cdar pi) a)
      (app (cdr pi) (caar pi)))
     (else (app (cdr pi) a)))))

(define (apply-pi pi t c e)
  (let rec ((t t))
    (cond
     ((nom? t) (app pi t))
     ((sus? t)
      (let ((pi (compose-pis pi (caddr t))))
        (if (id-pi? pi c e) t `(sus ,(cadr t) ,pi))))
     ((get-sus t c e)
      => (lambda (sus-c)
           (let ((pi (compose-pis pi (sus-pi sus-c))))
             (if (id-pi? pi c e) t `(sus ,t ,pi)))))
     ((var? t)
      (if (id-pi? pi c e) t `(sus ,t ,pi)))
     ((tie? t) 
      (make-tie (app pi (tie-a t))
                (rec (tie-t t))))
     ((pair? t) (cons (rec (car t)) (rec (cdr t))))
     (else t))))

#;
(define (reify-alpha-constraints v r c)
  (let ((c (filter-memq/rator '(sus-c hash) c)))
    (let ((c (reify-alpha r c)))
      (if (null? c) c `((alpha . ,c))))))

#;
(define (reify-alpha r c)
  (for/fold ([c^ '()])
            ([oc c])
    (cond
     ((reify-oc oc r)
      => (lambda (oc-sym)
           (if (member oc-sym c^) c^ (cons oc-sym c^))))
     (else c^))))


