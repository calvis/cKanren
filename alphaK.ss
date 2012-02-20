(library (alphaK)
  (export run run* == nom? project
    fresh-nom hash (rename (make-tie tie)) unify-s walk get-sus)

  (import
    (rnrs)
    (rnrs records syntactic)
    (only (mk)
      lambdag@ case-inf choiceg
      lambdaf@ inc bindg* empty-f project)
    (only (ck) empty-a size-s oc->rator oc->rands build-oc
      extend-reify-fns any/var? run run* fresh
      update-s update-c lambdam@ : composem goal-construct reify
      constrained-var constrained-var?)
    (only (chezscheme)
      trace-lambda
      gensym trace-define trace-define-syntax printf trace-let))

(define ==
  (lambda (u v)
    (goal-construct (unify-s u v))))

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
            ((and (pair? t) (eq? (car t) 'sus))
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
            ((and (var? t) (not (nom? t c)))
             ((composem (sus t `()) (rec t)) a))
            (else a)))))))

(define-syntax fresh-nom
  (syntax-rules ()
    ((_ (n ...) g0 g ...)
     (let ((n (constrained-var 'n 'a)) ...)
       (fresh () (nom n) ... g0 g ...)))))

(define-syntax letcc
  (syntax-rules ()
    ((_ k b0 b ...) (call/cc (lambda (k) b0 b ...)))))

(define-syntax make-pkg-f
  (syntax-rules ()
    ((_ s c) (cons s c))))

(define-syntax pkg-s
  (syntax-rules ()
    ((_ a) (car a))))

(define-syntax pkg-c
  (syntax-rules ()
    ((_ a) (cdr a))))

(define-syntax make-pkg
  (syntax-rules ()
    ((_ s c) (make-pkg-f s c))))

(define (make-var sym) (vector sym))
(define (var? sym) (vector? sym))

(define (sus-constrained? x oc)
  (and (eq? (oc->rator oc) 'sus-c)
       (eq? (sus-v oc) x)))

(define (sus? x c)
  (and (find (lambda (oc) (sus-constrained? x oc)) c) #t))

(define (get-sus x c)
  (find (lambda (oc) (sus-constrained? x oc)) c))

(define (sus-pi oc) (cadr (oc->rands oc)))
(define (sus-v oc) (car (oc->rands oc)))

(define sus-c
  (lambda (v pi)
    (lambdam@ (a : s c)
      (let ((v (walk v s c)))
        ((update-c (build-oc sus-c v pi)) a)))))

(define (make-tie a t) `(tie ,a ,t))
(define (tie? x) (and (pair? x) (eq? (car x) 'tie)))
(define (tie-a t) (cadr t))
(define (tie-t t) (caddr t))

(define (nom x) (goal-construct (nom-c x)))
(define (sus x pi) (goal-construct (sus-c x pi)))

(define (nom? x c)
  (and (find (lambda (oc) (nom-constrained? x oc)) c) #t))

(define (nom-constrained? x oc)
  (and (eq? (oc->rator oc) 'nom-c)
       (eq? (nom-v oc) x)))

(define (nom-v oc) (car (oc->rands oc)))

(define (nom-c x)
  (lambdam@ (a : s c)
    (let ((y (assq x s))) ;; hack
      (cond
        ((and y (nom? (cdr y) c))
         #f)
        (else ((update-c (build-oc nom-c x)) a))))))

(define ext-c
  (lambda (oc c)
    (cons oc c)))

(define unify-s
  (lambda (u v)
    (lambdam@ (a : s c)
      (let ((u (walk u s c)) (v (walk v s c)))
        (cond
          ((eq? u v) a)
          ((and (pair? u)
                (eq? (car u) 'sus))
           ((ext-s-nocheck (cadr u) (apply-pi (caddr u) v c)) a))
          ((get-sus u c)
           => (lambda (oc)
                ((ext-s-nocheck u (apply-pi (sus-pi oc) v c)) a)))
          ((and (pair? v)
                (eq? (car v) 'sus))
           ((ext-s-nocheck (cadr v) (apply-pi (caddr v) u c)) a))
          ((get-sus v c)
           => (lambda (oc)
                ((ext-s-nocheck v (apply-pi (sus-pi oc) u c)) a)))
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
          ((and (var? u) (not (nom? u c)))
           ((composem
              (sus u `())
              (ext-s-nocheck u (apply-pi `() v c)))
            a))
          ((and (var? v) (not (nom? v c)))
           ((composem
              (sus v `())
              (ext-s-nocheck v (apply-pi `() u c)))
            a))          
          ((or (nom? u c) (nom? v c)) #f)          
          ((equal? u v) a)
          (else #f))))))

(define ext-s
  (lambda (u v s)
    (cons `(,u . ,v) s)))

(define ext-s-nocheck
  (lambda (x t)
    (update-s x t)))

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
        ((nom? t c) (app pi t))
        ((and (pair? t)
              (eq? (car t) 'sus))
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

(define take
  (lambda (n f)
    (if (and n (zero? n))
        '()
        (case-inf (f)
          (() '())
          ((f) (take n f))
          ((a) (cons a '()))
          ((a f) (cons a (take (and n (- n 1)) f)))))))

(define reify-constraints-alpha
  (lambda (v r c)
    (let ((c (filter (lambda (oc) (case (oc->rator oc) ((sus-c nom-c hash-c) #t) (else #f))) c)))
      (let ((c (remp any/var? c)))
        (let ((c (fold-left (lambda (c oc)
                              (cond
                                ((reify-alpha-oc oc)
                                 => (lambda (oc^)
                                      (if (member oc^ c) c (cons oc^ c))))
                                (else c)))
                   '() c)))
          (if (null? c) c `((alpha . ,c))))))))

(define get
  (lambda (a s n c)
    (cond
      ((assq a s)
       => (lambda (a) (values (cdr a) s)))
      (else
        (let ((r (string->symbol 
                   (string-append 
                     n (number->string (c))))))
          (values r (cons (cons a r) s)))))))

(define reify-alpha-oc
  (lambda (oc)
    (case (oc->rator oc)
      ((hash-c)
       (let ((lhs (car (oc->rands oc)))
             (rhs (cadr (oc->rands oc))))
         (let ((rhs (if (and (pair? rhs) (eq? (car rhs) 'sus)) (cadr rhs) rhs)))
           `(hash (,lhs ,rhs)))))
      ((sus-c)  (and (not (null? (sus-pi oc))) `(sus ,(sus-v oc) ,(sus-pi oc))))
      (else #f))))

(define rwalk
  (lambda (t s)
    (cond
      ((assq t s) => cdr)
      (else t))))

(define-syntax let-pkg
  (syntax-rules ()
    ((_ (v) g0 g ...)
     (lambdag@ (a)
       (let ((v a))
         ((fresh-var () g0 g ...) a))))))

(extend-reify-fns 'alpha reify-constraints-alpha)

)