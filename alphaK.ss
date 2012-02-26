(library (alphaK)
  (export run run* == nom-constrained? project make-nom ==-check
    fresh-nom hash (rename (make-tie tie)) unify-s walk get-sus nom?)

  (import
    (rnrs)
    (rnrs records syntactic)
    (only (mk)
      lambdag@ case-inf choiceg var? take
      lambdaf@ inc bindg* empty-f project)
    (only (ck) empty-a size-s oc->rator oc->rands build-oc
      extend-reify-fns any/var? run run* fresh
      update-s update-c lambdam@ : composem goal-construct reify
      constrained-var constrained-var?)
    (only (chezscheme)
      trace-lambda
      gensym trace-define trace-define-syntax printf trace-let)
    (tracing))

(define make-nom
  (lambda (n)
    (constrained-var n 'a)))

(define-syntax fresh-nom
  (syntax-rules ()
    ((_ (n ...) g0 g ...)
     (let ((n (make-nom 'n)) ...)
       (fresh () (nom n) ... g0 g ...)))))

(define (sus-constrained? x oc)
  (and (eq? (oc->rator oc) 'sus-c)
       (eq? (sus-constraint-v oc) x)))

(define (sus-constraint-v oc) (car (oc->rands oc)))

(define (sus? x)
  (and (pair? x) (eq? (car x) 'sus)))

(define (get-sus x c)
  (let ((oc (find (lambda (oc) (sus-constrained? x oc)) c)))
    (and oc (cons 'sus (oc->rands oc)))))

(define (sus-v s)  (cadr s))
(define (sus-pi s) (caddr s))

(define sus-c
  (lambda (v pi)
    (lambdam@ (a : s c)
      (let ((v (walk v s c)))
        ((update-c (build-oc sus-c v pi)) a)))))

(define (make-tie a t) `(tie ,a ,t))
(define (tie? x) (and (pair? x) (eq? (car x) 'tie)))
(define (tie-a t) (cadr t))
(define (tie-t t) (caddr t))

(define nom
  (lambda (x)
    (goal-construct (nom-c x))))

(define sus
  (lambda (x pi)
    (goal-construct (sus-c x pi))))

(define (nom? x) (constrained-var? x))

(define (nom-constrained? x c)
  (and (find (lambda (oc) (nom-constraint? x oc)) c) #t))

(define (nom-constraint? x oc)
  (and (eq? (oc->rator oc) 'nom-c)
       (eq? (nom-v oc) x)))

(define (nom-v oc) (car (oc->rands oc)))

(define (nom-c x)
  (lambdam@ (a : s c)
    (let ((y (assq x s))) ;; hack
      (cond
        ((and y (nom? (cdr y))) #f)
        (else ((update-c (build-oc nom-c x)) a))))))

(define ==
  (lambda (u v)
    (goal-construct (unify-s u v))))

(define unify-s
  (lambda (u v)
    (lambdam@ (a : s c)
      (let ((u (walk u s c)) (v (walk v s c)))
        (cond
          ((eq? u v) a)
          ((sus? u)
           ((update-s (sus-v u) (apply-pi (sus-pi u) v c)) a))
          ((get-sus u c)
           => (lambda (s)
                ((update-s u (apply-pi (sus-pi s) v c)) a)))
          ((sus? v)
           ((update-s (sus-v v) (apply-pi (sus-pi v) u c)) a))
          ((get-sus v c)
           => (lambda (s)
                ((update-s v (apply-pi (sus-pi s) u c)) a)))
          ((and (tie? u) (tie? v))
           (let ((au (tie-a u)) (av (tie-a v))
                 (tu (tie-t u)) (tv (tie-t v)))
             (if (eq? au av)
                 ((unify-s tu tv) a)
                 ((composem
                    (hash-c au tv)
                    (unify-s tu (apply-pi `((,au . ,av)) tv c)))
                  a))))
          ((and (pair? u) (pair? v))
           ((composem
              (unify-s (car u) (car v))
              (unify-s (cdr u) (cdr v)))
            a))
          ((and (var? u) (not (nom? u)))
           ((composem
              (sus u `())
              (update-s u (apply-pi `() v c)))
            a))
          ((and (var? v) (not (nom? v)))
           ((composem
              (sus v `())
              (update-s v (apply-pi `() u c)))
            a))          
          ((or (nom? u) (nom? v)) #f)          
          ((equal? u v) a)
          (else #f))))))

(define ==-check
  (lambda (u v)
    (goal-construct (unify-s-check u v))))

(define unify-s-check
  (lambda (u v)
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
                 ((composem
                    (hash-c au tv)
                    (unify-s-check tu (apply-pi `((,au . ,av)) tv c)))
                  a))))
          ((and (pair? u) (pair? v))
           ((composem
              (unify-s-check (car u) (car v))
              (unify-s-check (cdr u) (cdr v)))
            a))
          ((and (var? u) (not (nom? u)))
           ((composem
              (sus u `())
              (ext-s-check u (apply-pi `() v c)))
            a))
          ((and (var? v) (not (nom? v)))
           ((composem
              (sus v `())
              (ext-s-check v (apply-pi `() u c)))
            a))          
          ((or (nom? u) (nom? v)) #f)
          ((equal? u v) a)
          (else #f))))))

(define ext-s-check
  (lambda (x u)
    (lambdam@ (a : s c)
      (and (occurs-check x u s c)
           ((update-s x u) a)))))

(define occurs-check
  (lambda (x t s c)
    (let rec ([t t])
      (let ([t (walk (tie-t* t) s c)])
        (cond
          [(sus? t) (not (eq? x (sus-v t)))]
          [(get-sus t c)
           => (lambda (sus-c)
                (not (eq? x (sus-v sus-c))))]
          [(pair? t) (and (rec (car t)) (rec (cdr t)))]
          [else #t])))))

(define hash
  (lambda (b t)
    (goal-construct (hash-c b t))))

(define hash-c
  (lambda (b t)
    (let rec ((t t))
      (lambdam@ (a : s c)
        (let ((t (walk t s c)))
          (cond
            ((eq? b t) #f)
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
             ((composem (rec (car t)) (rec (cdr t))) a))
            ((and (var? t) (not (nom? t)))
             ((composem (sus t `()) (rec t)) a))
            (else a)))))))

(define tie-t*
  (lambda (t)
    (if (tie? t) (tie-t* (tie-t t)) t)))

(define walk-sym
  (lambda (v s)
    (let loop ((s s))
      (cond
        ((null? s) #f)
        ((eq? v (caar s)) (car s))
        (else (loop (cdr s)))))))

(define walk
  (lambda (x s c)
    (let f ((x x) (pi '()))
      (cond
        ((sus? x)
         (cond
           ((walk-sym (sus-v x) s)
            => (lambda (a) (f (cdr a) (compose-pis (sus-pi x) pi))))
           (else (apply-pi pi x c))))
        ((get-sus x c)
         => (lambda (sus-c)
              (cond
                ((walk-sym x s)
                 => (lambda (a)
                      (f (cdr a) 
                        (compose-pis (sus-pi sus-c) pi))))
                (else (apply-pi pi x c)))))
        (else (apply-pi pi x c))))))

(define walk*
  (lambda (t s c)
    (let ((t (walk t s c)))
      (cond
        ((tie? t)
         (make-tie (tie-a t) (walk* (tie-t t) s c)))
        ((pair? t)
         (cons (walk* (car t) s c) (walk* (cdr t) s c)))
        (else t)))))

(define compose-pis append)

(define get-noms
  (let ((with (lambda (n s) (if (memq n s) s (cons n s)))))
    (lambda (pi s)
      (cond
        ((null? pi) s)
        (else
          (get-noms (cdr pi)
            (with (caar pi) (with (cdar pi) s))))))))

(define pi-ds
  (lambda (pi1 pi2 c)
    (fold-left
      (lambda (s nom)
        (cond
          ((eq? (apply-pi pi1 nom c) (apply-pi pi2 nom c)) s)
          (else (cons nom s))))
      '()
      (get-noms pi1 (get-noms pi2 '())))))

(define id-pi?
  (lambda (pi c) (null? (pi-ds pi '() c))))

(define app
  (lambda (pi a)
    (let ((pi (reverse pi)))
      (cond
        ((null? pi) a)
        ((eq? (caar pi) a)
         (app (cdr pi) (cdar pi)))
        ((eq? (cdar pi) a)
         (app (cdr pi) (caar pi)))
        (else (app (cdr pi) a))))))

(define apply-pi
  (lambda (pi t c)
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
        (else t)))))

(define alpha-constraint?
  (lambda (oc)
    (memq (oc->rator oc) '(sus-c nom-c hash-c))))

(define reify-alpha-constraints
  (lambda (v r c)
    (let ((c (filter alpha-constraint? c)))
      (let ((c (remp any/var? c)))
        (let ((c (fold-left reify-alpha-oc `() c)))
          (if (null? c) c `((alpha . ,c))))))))

(define reify-alpha-oc
  (lambda (c oc)
    (cond
      ((reify-oc oc)
       => (lambda (oc^)
            (if (member oc^ c) c (cons oc^ c))))
      (else c))))

(define reify-oc
  (lambda (oc)
    (case (oc->rator oc)
      ((hash-c)
       (let ((lhs (car (oc->rands oc)))
             (rhs (cadr (oc->rands oc))))
         (let ((rhs (if (sus? rhs) (cadr rhs) rhs)))
           `(hash (,lhs ,rhs)))))
      (else #f))))

(extend-reify-fns 'alpha reify-alpha-constraints)

)