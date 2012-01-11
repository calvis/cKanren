(library 
  (ck)

  (export
    ;; framework
    update-s update-c make-a any/var? prefix-s
    lambdam@ identitym composem goal-construct ext-c
    build-oc oc->proc oc->rands oc->rator run run* prt
    extend-enforce-fns extend-reify-fns

    ;; mk
    lhs rhs walk walk* var? lambdag@ mzerog unitg onceo
    conde conda condu ifa ifu project fresh :)
  
  (import (rnrs) (mk)
    (only (chezscheme) make-parameter))

;; ---HELPERS------------------------------------------------------

(define any/var?
  (lambda (p)
    (cond
      ((var? p) #t)
      ((pair? p)
       (or (any/var? (car p)) (any/var? (cdr p))))
      (else #f))))

(define any-relevant/var?
  (lambda (t x*)
    (cond
      ((var? t) (memq t x*))
      ((pair? t)
       (or (any-relevant/var? (car t) x*)
           (any-relevant/var? (cdr t) x*)))
      (else #f))))

(define prefix-s
  (lambda (s s^)
    (cond
      ((null? s) s^)
      (else
        (let loop ((s^ s^))
          (cond
            ((eq? s^ s) '())
            (else (cons (car s^) (loop (cdr s^))))))))))

;; ---SUBSITUTION--------------------------------------------------

(define empty-s '())

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define size-s
  (lambda (x)
    (length x)))

(define update-s-check
  (lambda (x v)
    (lambdam@ (a : s c)
      (let ((x (walk x s))
            (v (walk v s)))
        (cond
          ((or (var? x) (var v))
           (let ((s^ (ext-s x v s)))
             ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
              (make-a s^ c))))
          ((equal? x v) a)
          (else #f))))))

(define update-s-nocheck
  (lambda (x v)
    (lambdam@ (a : s c)
      ((run-constraints (if (var? v) `(,x ,v) `(,x)) c)
       (make-a (ext-s x v s) c)))))

(define update-s update-s-nocheck)

;; ---CONSTRAINT-STORE---------------------------------------------

(define empty-c '())

(define ext-c
  (lambda (oc c)
    (cons oc c)))

(define update-c
  (lambda (oc)
    (lambdam@ (a : s c)
      (cond
        ((any/var? (oc->rands oc))
         (make-a s (ext-c oc c)))
        (else a)))))

;; ---PACKAGE------------------------------------------------------

(define empty-a (cons empty-s empty-c))
(define make-a (lambda (s c) (cons s c)))

;; ---M-PROCS------------------------------------------------------

(define-syntax lambdam@
  (syntax-rules (:)
    ((_ (a) e) (lambda (a) e))
    ((_ (a : s c) e)
     (lambdam@ (a) (let ((s (car a)) (c (cdr a))) e)))))

(define identitym (lambdam@ (a) a))

(define composem
  (lambda (fm f^m)
    (lambdam@ (a)
      (let ((a (fm a)))
        (and a (f^m a))))))

(define goal-construct
  (lambda (fm)
    (lambdag@ (a)
      (cond
        ((fm a) => unitg)
        (else (mzerog))))))

;; ---BUILD-OC-----------------------------------------------------

(define-syntax build-oc
  (syntax-rules ()
    ((_ op arg ...)
     (build-oc-aux op (arg ...) () (arg ...)))))

(define-syntax build-oc-aux
  (syntax-rules ()
    ((_ op () (z ...) (arg ...))
     (let ((z arg) ...) `(,(op z ...) . (op ,z ...))))
    ((_ op (arg0 arg ...) (z ...) args)
     (build-oc-aux op (arg ...) (z ... q) args))))

(define oc->proc car)
(define oc->rands cddr)
(define oc->rator cadr)

;; ---FIXED-POINT--------------------------------------------------

(define run-constraints
  (lambda (x* c)
    (cond
      ((null? c) identitym)
      ((any-relevant/var? (oc->rands (car c)) x*)
       (composem
         (rem/run (car c))
         (run-constraints x* (cdr c))))
      (else (run-constraints x* (cdr c))))))

(define rem/run
  (lambda (oc)
    (lambdam@ (a : s c)
      (cond
        ((memq oc c)
         ((oc->proc oc)
          (make-a s (remq oc c))))
        (else a)))))

;; ---PARAMETERS---------------------------------------------------

(define enforce-fns (make-parameter '()))
(define reify-fns (make-parameter '()))

(define extend-parameter
  (lambda (param)
    (lambda (tag fn)
      (let ((fns (param)))
        (and (not (assq tag fns))
             (param (cons `(,tag . ,fn) fns)))))))

(define extend-enforce-fns (extend-parameter enforce-fns))
(define extend-reify-fns (extend-parameter reify-fns))

;; ---ENFORCE-CONSTRAINTS------------------------------------------

(define enforce-constraints
  (lambda (x)
    (let loop ((fns (enforce-fns)))
      (cond
        ((null? fns) unitg)
        (else
          (fresh ()
            ((cdar fns) x)
            (loop (cdr fns))))))))

;; ---REIFICATION--------------------------------------------------

(define reify-s
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) `((,v . ,(reify-n (size-s s))) . ,s))
        ((pair? v) (reify-s (cdr v) (reify-s (car v) s)))
        (else s)))))

(define reify-n
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define reify
  (lambda (x)
    (lambdag@ (a : s c)
      (let* ((v (walk* x s))
             (r (reify-s v empty-s)))
        (cond
          ((null? r) (choiceg v empty-f))
          (else
            (let ((v (walk* v r)))
              (reify-constraints v r c))))))))

(define reify-constraints
  (lambda (v r c)
    (choiceg
      (cond
        ((null? c) v)
        (else
          (let ((c^ (run-reify-fns v r c)))
            (cond
              ((null? c^) v)
              (else `(,v : . ,c^))))))
      empty-f)))

(define run-reify-fns
  (lambda (v r c)
    (let loop ((fns (reify-fns)) (c c))
      (cond
        ((null? fns) c)
        (else (loop (cdr fns) ((cdar fns) v r c)))))))

;; ---MACROS-------------------------------------------------------

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g1 ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g1 ...
            (enforce-constraints x) (reify x))
          empty-a))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

;; ----------------------------------------------------------------

)

(import (ck))
