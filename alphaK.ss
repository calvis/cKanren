(library (alphaK)
  (export run run* == nom? project var->sus
    fresh-nom hash (rename (make-tie tie)) unify-s walk get-sus)

  (import
    (rnrs)
    (rnrs records syntactic)
    (only (mk)
      lambdag@ case-inf choiceg
      lambdaf@ inc bindg* empty-f project)
    (only (ck) empty-a size-s oc->rator oc->rands build-oc
      extend-reify-fns any/var? run run* fresh
      update-s update-c lambdam@ : composem goal-construct reify)
    (rename (only (ck) walk*) (walk* ck:walk*))
    (only (chezscheme) gensym trace-define trace-define-syntax printf trace-let))

(define ==
  (lambda (u v)
    (goal-construct (unify-s u v))))

(define hash
  (lambda (b t)
    (goal-construct (hash-c b t))))

(define hash-c
  (lambda (b t)
    (trace-let rec ((t t))
      (lambdam@ (a : s c)
        (let ((t (walk t s c)))
          (cond
            ((eq? b t) #f)
            ((get-sus t c)
             => (lambda (sus-c)
                  (let ((lhs (apply-pi (sus-pi sus-c) b c)))
                    ((update-c (build-oc hash-c lhs t)) a))))
            ((tie? t)
             (if (eq? b (tie-a t)) a ((rec (tie-t t)) a)))
            ((pair? t)
             ((composem (rec (car t)) (rec (cdr t))) a))
            (else a)))))))

(define-syntax fresh-nom
  (syntax-rules ()
    ((_ (n ...) g0 g ...)
     (fresh (n ...)
       (nom n) ... g0 g ...))))

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

(define (var->sus var)
  (make-sus var '()))

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

(define (make-sus v pi)
  `(,(lambda (x) x) sus-c ,v ,pi))

(define (make-tie a t) `(tie ,a ,t))
(define (tie? x) (and (pair? x) (eq? (car x) 'tie)))
(define (tie-a t) (cadr t))
(define (tie-t t) (caddr t))

(define (nom x) (goal-construct (nom-c x)))

(define (nom? x c)
  (and (find (lambda (oc) (nom-constrained? x oc)) c) #t))

(define (nom-constrained? x oc)
  (and (eq? (oc->rator oc) 'nom-c)
       (eq? (nom-v oc) x)))

(define (nom-v oc) (car (oc->rands oc)))

(define (nom-c x)
  (lambdam@ (a : s c)
    (let ((x (walk x s c)))
      ((update-c (build-oc nom-c x)) a))))

;; GONE
;; (define-record-type sus (fields pi (mutable v)))
;; (define-record-type var
;;   (parent sus) (fields name)
;;   (protocol (lambda (make-sus)
;;               (lambda (name)
;;                 (let ((var ((make-sus '() #f) name)))
;;                   (sus-v-set! var var) var)))))

;; (define-record-type nom (fields name))

;; GONE
;; (define-record-type tie (fields a t))

(define tie-t*
  (lambda (t)
    (if (tie? t) (tie-t* (tie-t t)) t)))

(define ext-h*
  (lambda (a v c)
    (let ((h (cons a v)))
      (if (member h c) c (cons h c)))))

(define ext-c
  (lambda (oc c)
    (cons oc c)))

;; (define ds-ext-c
;;   (lambda (ds v c)
;;     (fold-left (lambda (c x) (ext-c x v c)) c ds)))

(define unify-s
  (lambda (u v)
    (lambdam@ (a : s c)
      (let ((u (walk u s c)) (v (walk v s c)))
        (cond
          ((eq? u v) a)

          ;; if they're both variables, and the symbol they represent
          ;; is the same, then do some stuff
          ;; ((and (sus? u) (sus? v)
          ;;       (eq? (sus-v u) (sus-v v)))
          ;;  (printf "Here\n")
          ;;  (let ((c (ds-ext-c
          ;;             (pi-ds (sus-pi u) (sus-pi v))
          ;;             (sus-v u)
          ;;             c)))
          ;;    (make-pkg s c)))

          ;; if the first is a variable, or the second is a variable,
          ;; extend the substitution
          ((get-sus u c)
           => (lambda (usus-c)
                ((ext-s-nocheck u (apply-pi (sus-pi usus-c) v c)) a)))
          ((get-sus v c)
           => (lambda (sus-c)
                ((ext-s-nocheck v (apply-pi (sus-pi sus-c) u c)) a)))

          ;; ((sus? u)
          ;;  (ext-s-nocheck (sus-v u) (apply-pi (sus-pi u) v) a))

          ;; ((sus? v)
          ;;  (ext-s-nocheck (sus-v v) (apply-pi (sus-pi v) u) a))

          ;; if they're both ties, check to see if the a's are the
          ;; same -- if they are, just unify the t's.  if not, run
          ;; hash-check on the first a and the second t. get a new
          ;; constraint store back, and try to unify some things.
          ((and (tie? u) (tie? v))
           (let ((au (tie-a u)) (av (tie-a v))
                 (tu (tie-t u)) (tv (tie-t v)))
             (if (eq? au av)
                 ((unify-s tu tv) a)
                 ((composem
                    (hash-c au tv)
                    (unify-s tu
                      (apply-pi `((,au . ,av)) tv c)))
                  a))))
          
          ((and (pair? u) (pair? v))
           ((composem
              (unify-s (car u) (car v))
              (unify-s (cdr u) (cdr v)))
            a))
          
          ((and (var? u) (not (nom? u c)))
           (let ((c (cons (var->sus u) c)))
             ((unify-s v u) (make-pkg s c))))
          ((and (var? v) (not (nom? v c)))
           (let ((c (cons (var->sus v) c)))
             ((unify-s u v) (make-pkg s c))))
          
          ((or (nom? u c) (nom? v c)) #f)
          
          ((equal? u v) a)
          (else #f))))))

(define ext-s
  (lambda (u v s)
    (cons `(,u . ,v) s)))

(define ext-s-nocheck
  (lambda (x t)
    (lambdam@ (a : s c)
      ((update-s x t) a))))

(define (get-h* c)
  (cond
    ((find (lambda (oc) (eq? (oc->rator oc) 'verify-h*)) c)
     => (lambda (oc) (cdr (oc->rands oc))))
    (else `())))

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
        ;; ((and (sus? x) (walk-sym (sus-v x) s))
        ;;  => (lambda (a)
        ;;       (walk (cdr a) 
        ;;         (compose-pis (sus-pi x) pi))))
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
        ;; ((sus? t)
        ;;  (let ((pi (compose-pis pi (sus-pi t))))
        ;;    (if (id-pi? pi)
        ;;        (sus-v t)
        ;;        (make-sus pi (sus-v t)))))
        ((get-sus t c)
         => (lambda (sus-c)
              (let ((pi (compose-pis pi (sus-pi sus-c))))
                (if (id-pi? pi c) t (make-sus t pi)))))
        ((tie? t) (make-tie (app pi (tie-a t))
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
      (let ((c (ck:walk* c r)))
        (let-values (((v^ s) (reify-vars/noms v r c)))
          (let ((c (discard/reify-c c s)))
            (values
              (if (eq? v v^) #f v^)
              (if (null? c) c `(alpha : ,c)))))))))

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

(define reify-vars/noms
  (let
      ((counter
         (lambda ()
           (let ((n -1)) (lambda () (set! n (+ n 1)) n)))))
    (lambda (t s c)
      (let ((sc (counter)) (nc (counter)))
        (let rec ((t t) (s s))
          (cond

            ;; ((sus? t)
            ;;  (let ((pi (sus-pi t)))
            ;;    (let-values
            ;;        (((v s) (get (sus-v t) s "_." sc)))
            ;;      (if (null? pi) (values v s)
            ;;          (let-values (((pi s) (rec pi s)))
            ;;            (values `(sus ,pi ,v) s))))))
            
            ((get-sus t c)
             => (lambda (sus-c)
                  (let ((pi (sus-pi sus-c)))
                    (let-values
                        (((v s) (get t s "_." sc)))
                      (if (null? pi)
                          (values v s)
                          (let-values (((pi s) (rec pi s)))
                            (values `(sus ,pi ,v) s)))))))

            ((nom? t c) (get t s "a." nc))
            ((tie? t)
             (let-values (((a s) (rec (tie-a t) s)))
               (let-values (((t s) (rec (tie-t t) s)))
                 (values `(tie ,a ,t) s))))
            ((pair? t)
             (let-values (((a s) (rec (car t) s)))
               (let-values (((d s) (rec (cdr t) s)))
                 (values (cons a d) s))))
            ((var? t)
             (let-values (((v s) (get t s "_." sc)))
               (values v s)))
            (else (values t s))))))))

(define rwalk
  (lambda (t s)
    (cond
      ((assq t s) => cdr)
      (else t))))

(define discard/reify-c
  (lambda (c s)
    (let
        ((vs->rs
           (lambda (vs)
             (let loop ((vs vs) (rs '()))
               (cond
                 ((null? vs) rs)
                 (else
                   (let ((r (rwalk (car vs) s)))
                     (if (get-sus r c)
                         (loop (cdr vs) rs)
                         (loop (cdr vs) `(,r . ,rs)))))))))
         (collate-vs
           (let
               ((remdups
                  (lambda (l)
                    (let loop ((l l) (s '()))
                      (cond
                        ((null? l) (reverse s))
                        ((memq (car l) s) (loop (cdr l) s))
                        (else (loop (cdr l)
                                (cons (car l) s))))))))
             (lambda (a c)
               (let loop ((c c) (vs '()) (r* '()))
                 (cond
                   ((null? c) (values (remdups vs) r*))
                   ((eq? (caar c) a)
                    (loop (cdr c) (cons (cdar c) vs) r*))
                   (else
                     (loop (cdr c) vs
                       (cons (car c) r*)))))))))
      (let loop ((c c) (r* '()))
        (cond
          ((null? c) r*)
          (else
            (let ((a (caar c)))
              (or
                (letcc f
                  (let ((r (cond ((assq a s) => cdr)
                                 (else (f #f)))))
                    (let-values
                        (((vs c) (collate-vs a c)))
                      (let ((rs (vs->rs vs)))
                        (if (null? rs)
                            (f #f)
                            (loop
                              c `((,r . ,rs) . ,r*)))))))
                (loop (cdr c) r*)))))))))

(define-syntax let-pkg
  (syntax-rules ()
    ((_ (v) g0 g ...)
     (lambdag@ (a)
       (let ((v a))
         ((fresh-var () g0 g ...) a))))))

(extend-reify-fns 'alpha reify-constraints-alpha)

)
