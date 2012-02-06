(library (alphaK)
  (export run run* == ==-check fresh make-nom nom? project
          fresh-nom hash (rename (make-tie tie))) 

(import
  (rnrs)
  (rnrs records syntactic)
  (only (mk) lambdag@ case-inf choiceg lambdaf@ inc bindg* empty-f)
  (only (chezscheme) gensym trace-define printf))

(define-syntax run
  (syntax-rules ()
    [(_ n (q) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (q)
            g0 g ...
            (lambdag@ (p)
              (reify q p)))
          empty-pkg)))]))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g0 g ...)
     (run #f (x) g0 g ...))))

(define ==
  (lambda (u v)
    (lambdag@ (a)
      (let ([a^ (unify-s u v a)])
        (and a^
          (letcc f
            (let ([h* (verify-h* a^ f)])
              (make-pkg a^ (h* . ,h*)))))))))

(define ==-check
  (lambda (u v)
    (lambdag@ (a)
      (let ([a^ (unify-s-check u v a)])
        (and a^
          (letcc f
            (let ([h* (verify-h* a^ f)])
              (make-pkg a^ (h* . ,h*)))))))))

(define hash
  (lambda (b t)
    (lambdag@ (a)
      (letcc f
        (let ([h* (hash-check b t (pkg-s a) (pkg-h* a) f)])
          (make-pkg a (h* . ,h*)))))))

(define-syntax fresh
  (syntax-rules ()
    [(_ (e ...) g0 g ...)
     (lambdag@ (a)
       (inc
         (let ([e (make-var 'e (pkg-s a))] ...)
           (bindg* (g0 a) g ...))))]))

(define-syntax fresh-nom
  (syntax-rules ()
    [(_ (n ...) g0 g ...)
     (lambdag@ (a)
       (inc
         (let ([n (make-nom 'n)] ...)
           (bindg* (g0 a) g ...))))]))

(define-syntax letcc
  (syntax-rules ()
   [(_ k b0 b ...) (call/cc (lambda (k) b0 b ...))]))

(define-record-type (pkg make-pkg-f pkg?)
  (fields s h*)
  (protocol
    (lambda (make-pkg)
      (lambda (pkg . fields)
        (letrec-syntax
          ([with-fields
             (syntax-rules ()
               [(_ (s0 ...) (f0 ...) body)
                (let ([s0 (cond
                            [(assq 's0 fields) => cdr]
                            [else (f0 pkg)])]
                      ...)
                  body)])])
          (with-fields (s h*) (pkg-s pkg-h*)
            (make-pkg s h*)))))))

(define-syntax make-pkg
  (syntax-rules (h*)
    [(_ pkg (a . d) ...)
     (make-pkg-f pkg `(a . d) ...)]))

(define empty-s '())
(define empty-pkg
  (make-pkg #f (s . ,empty-s) (h* . ())))

(define-record-type sus (fields pi (mutable v)))
(define-record-type var
  (parent sus) (fields name s)
  (protocol (lambda (make-sus)
              (lambda (name s)
                (let ([var ((make-sus '() #f) name s)])
                  (sus-v-set! var var) var)))))
(define-record-type nom (fields name))
(define-record-type tie (fields a t))

(define tie-t*
  (lambda (t)
    (if (tie? t) (tie-t* (tie-t t)) t)))

(define ext-h*
  (lambda (a v h*)
    (let ([h (cons a v)])
      (if (member h h*) h*
        (cons h h*)))))

(define s-size length)

(define unify-s
  (letrec ([ds-ext-h*
             (lambda (ds v h*)
               (let loop ([ds ds] [h* h*])
                 (cond
                   [(null? ds) h*]
                   [else 
                     (loop (cdr ds)
                           (ext-h* (car ds) v h*))])))])
    (lambda (u v a)
      (let ([s (pkg-s a)])
        (let ([u (walk u s)] [v (walk v s)])
          (cond
            [(eq? u v) a]
            [(and (sus? u) (sus? v)
                  (eq? (sus-v u) (sus-v v)))
             (let ([h* (ds-ext-h*
                         (pi-ds (sus-pi u) (sus-pi v))
                         (sus-v u)
                         (pkg-h* a))])
               (make-pkg a (h* . ,h*)))]
            [(sus? u)
             (ext-s-nocheck
               ;; does this pi need to be reversed, or
               ;; does that happen automatically?
               (sus-v u) (apply-pi (sus-pi u) v) a)]
            [(sus? v)
             (ext-s-nocheck
               (sus-v v) (apply-pi (sus-pi v) u) a)]
            [(and (pair? u) (pair? v))
             (let ([a (unify-s (car u) (car v) a)])
               (and a (unify-s (cdr u) (cdr v) a)))]
            [(and (tie? u) (tie? v))
             (let ([au (tie-a u)] [av (tie-a v)]
                                  [tu (tie-t u)] [tv (tie-t v)])
               (if (eq? au av) (unify-s tu tv a)
                 (letcc f
                   (let ([h* (hash-check
                               au tv s (pkg-h* a) f)])
                     (unify-s
                       tu (apply-pi `((,au . ,av)) tv)
                       (make-pkg a (h* . ,h*)))))))]
            [(or (nom? u) (nom? v)) #f]
            [(equal? u v) a]
            [else #f]))))))

(define unify-s-check
  (letrec ([ds-ext-h*
             (lambda (ds v h*)
               (let loop ([ds ds] [h* h*])
                 (cond
                   [(null? ds) h*]
                   [else 
                     (loop (cdr ds)
                           (ext-h* (car ds) v h*))])))])
    (lambda (u v a)
      (let ([s (pkg-s a)])
        (let ([u (walk u s)] [v (walk v s)])
          (cond
            [(eq? u v) a]
            [(and (sus? u) (sus? v)
                  (eq? (sus-v u) (sus-v v)))
             (let ([h* (ds-ext-h*
                         (pi-ds (sus-pi u) (sus-pi v))
                         (sus-v u)
                         (pkg-h* a))])
               (make-pkg a (h* . ,h*)))]
            [(sus? u)
             (ext-s-check
               ;; does this pi need to be reversed, or
               ;; does that happen automatically?
               (sus-v u) (apply-pi (sus-pi u) v) a)]
            [(sus? v)
             (ext-s-check
               (sus-v v) (apply-pi (sus-pi v) u) a)]
            [(and (pair? u) (pair? v))
             (let ([a (unify-s-check (car u) (car v) a)])
               (and a (unify-s-check (cdr u) (cdr v) a)))]
            [(and (tie? u) (tie? v))
             (let ([au (tie-a u)] [av (tie-a v)]
                                  [tu (tie-t u)] [tv (tie-t v)])
               (if (eq? au av) (unify-s-check tu tv a)
                 (letcc f
                   (let ([h* (hash-check
                               au tv s (pkg-h* a) f)])
                     (unify-s-check
                       tu (apply-pi `((,au . ,av)) tv)
                       (make-pkg a (h* . ,h*)))))))]
            [(or (nom? u) (nom? v)) #f]
            [(equal? u v) a]
            [else #f]))))))

(define ext-s
  (lambda (u v s)
    (cons `(,u . ,v) s)))

(define ext-s-check
  (lambda (x t a)
    (let ([s (pkg-s a)])
      (and (occurs-check x t s)
           (let ([s (ext-s x t s)])
             (make-pkg a (s . ,s)))))))

(define ext-s-nocheck
  (lambda (x t a)
    (let ([s (pkg-s a)])
      (let ([s (ext-s x t s)])
        (make-pkg a (s . ,s))))))

(define occurs-check
  (lambda (x t s)
    (let rec ([t t])
      (let ([t (walk (tie-t* t) s)])
        (cond
          [(sus? t) (not (eq? x (sus-v t)))]
          [(pair? t) (and (rec (car t)) (rec (cdr t)))]
          [else #t])))))

(define verify-h*
  (lambda (a f)
    (let loop ([h* (pkg-h* a)] [a* '()])
      (cond
        [(null? h*) a*]
        [else
          (loop (cdr h*)
            (hash-check
              (caar h*) (cdar h*) (pkg-s a) a* f))]))))

(define hash-check
  (lambda (a t s h* f)
    (let rec ([t t] [h* h*])
      (let ([t (walk t s)])
        (cond
          [(eq? a t) (f #f)]
          [(sus? t)
           (ext-h* (apply-pi (sus-pi t) a) (sus-v t) h*)]
          [(and (tie? t) (not (eq? a (tie-a t))))
           (rec (tie-t t) h*)]
          [(pair? t)
           (rec (cdr t) (rec (car t) h*))]
          [else h*])))))

(define walk
  (lambda (x s)
    (let ([find (lambda (v)
                  (let loop ([s s])
                    (cond
                      [(eq? (var-s v) s) #f]
                      [(eq? v (caar s)) (car s)]
                      [else (loop (cdr s))])))])
      (let walk ([x x] [pi '()])
        (cond
          [(and (sus? x) (find (sus-v x)))
           => (lambda (a)
                (walk (cdr a) 
                      (compose-pis (sus-pi x) pi)))]
          [else (apply-pi pi x)])))))

(define walk*
  (lambda (t s)
    (let ([t (walk t s)])
      (cond
        [(tie? t)
         (make-tie (tie-a t) (walk* (tie-t t) s))]
        [(pair? t)
         (cons (walk* (car t) s) (walk* (cdr t) s))]
        [else t]))))

(define compose-pis append)

(define pi-ds
  (letrec
    ([get-noms
       (let ([with (lambda (n s)
                     (if (memq n s) s (cons n s)))])
         (lambda (pi s)
           (cond
             [(null? pi) s]
             [else
               (get-noms (cdr pi)
                 (with (caar pi) (with (cdar pi) s)))])))])
    (lambda (pi1 pi2)
      (let loop ([noms (get-noms pi1 (get-noms pi2 '()))]
                 [s '()])
        (cond
          [(null? noms) s]
          [else (let ([a (car noms)])
                  (if (eq? (apply-pi pi1 a)
                           (apply-pi pi2 a))
                    (loop (cdr noms) s)
                    (loop (cdr noms) (cons a s))))])))))

(define id-pi?
  (lambda (pi) (null? (pi-ds pi '()))))

(define apply-pi
  (lambda (pi t)
    (letrec ([app (lambda (pi a)
                    (let ([pi (reverse pi)])
                      (cond
                        [(null? pi) a]
                        [(eq? (caar pi) a)
                         (app (cdr pi) (cdar pi))]
                        [(eq? (cdar pi) a)
                         (app (cdr pi) (caar pi))]
                        [else (app (cdr pi) a)])))])
      (let rec ([t t])
        (cond
          [(nom? t) (app pi t)]
          [(sus? t)
           (let ([pi (compose-pis pi (sus-pi t))])
             (if (id-pi? pi)
                 (sus-v t)
                 (make-sus pi (sus-v t))))]
          [(tie? t) (make-tie (app pi (tie-a t))
                              (rec (tie-t t)))]
          [(pair? t) (cons (rec (car t)) (rec (cdr t)))]
          [else t])))))

(define take
  (lambda (n f)
    (if (and n (zero? n))
      '()
      (case-inf (f)
        [() '()]
        [(f) (take n f)]
        [(a) (cons a '())]
        [(a f) (cons a (take (and n (- n 1)) f))]))))

(define reify
  (lambda (x a)
    (let ([s (pkg-s a)])
      (let ([x (walk* x s)])
        (let-values ([(x s) (reify-vars/noms x)])
          (let ([h* (discard/reify-h* (pkg-h* a) s)])
            (choiceg (if (null? h*) x `(,x : ,h*)) empty-f)))))))

(define reify-vars/noms
  (let
    ([counter
       (lambda ()
         (let ([n -1]) (lambda () (set! n (+ n 1)) n)))])
    (let ([get (lambda (a s n c)
                 (cond
                   [(assq a s)
                    => (lambda (a) (values (cdr a) s))]
                   [else
                     (let ([r (string->symbol 
                                (string-append 
                                  n (number->string (c))))])
                       (values r (cons (cons a r) s)))]))])
      (lambda (t)
        (let ([sc (counter)] [nc (counter)])
          (let rec ([t t] [s '()])
            (cond
              [(sus? t)
               (let ([pi (sus-pi t)])
                 (let-values
                   ([(v s) (get (sus-v t) s "_." sc)])
                   (if (null? pi) (values v s)
                     (let-values ([(pi s) (rec pi s)])
                       (values `(sus ,pi ,v) s)))))]
              [(nom? t) (get t s "a." nc)]
              [(tie? t)
               (let-values ([(a s) (rec (tie-a t) s)])
                 (let-values ([(t s) (rec (tie-t t) s)])
                   (values `(tie ,a ,t) s)))]
              [(pair? t)
               (let-values ([(a s) (rec (car t) s)])
                 (let-values ([(d s) (rec (cdr t) s)])
                   (values (cons a d) s)))]
              [else (values t s)])))))))

(define rwalk
  (lambda (t s)
    (cond
      [(assq t s) => cdr]
      [else t])))

(define discard/reify-h*
  (lambda (h* s)
    (let
      ([vs->rs
         (lambda (vs)
           (let loop ([vs vs] [rs '()])
             (cond
               [(null? vs) rs]
               [else
                 (let ([r (rwalk (car vs) s)])
                   (if (sus? r)
                     (loop (cdr vs) rs)
                     (loop (cdr vs) `(,r . ,rs))))])))]
       [collate-vs
         (let
           ([remdups
              (lambda (l)
                (let loop ([l l] [s '()])
                  (cond
                    [(null? l) (reverse s)]
                    [(memq (car l) s) (loop (cdr l) s)]
                    [else (loop (cdr l)
                                (cons (car l) s))])))])
           (lambda (a h*)
             (let loop ([h* h*] [vs '()] [r* '()])
               (cond
                 [(null? h*) (values (remdups vs) r*)]
                 [(eq? (caar h*) a)
                  (loop (cdr h*) (cons (cdar h*) vs) r*)]
                 [else
                   (loop (cdr h*) vs
                         (cons (car h*) r*))]))))])
      (let loop ([h* h*] [r* '()])
        (cond
          [(null? h*) r*]
          [else
            (let ([a (caar h*)])
              (or
                (letcc f
                  (let ([r (cond [(assq a s) => cdr]
                                 [else (f #f)])])
                    (let-values
                      ([(vs h*) (collate-vs a h*)])
                      (let ([rs (vs->rs vs)])
                        (if (null? rs) (f #f)
                          (loop
                            h* `((,r . ,rs) . ,r*)))))))
                (loop (cdr h*) r*)))])))))

(define-syntax project
  (syntax-rules ()
    [(_ (x ...) g0 g ...)
     (lambdag@ (a)
       (let ([x (walk* x (pkg-s a))] ...)
         ((fresh () g0 g ...) a)))]))

(define-syntax let-pkg
  (syntax-rules ()
    [(_ (v) g0 g ...)
     (lambdag@ (a)
       (let ([v a])
         ((fresh () g0 g ...) a)))])))
