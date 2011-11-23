(library
  (mk)

  (export
    var var? rhs lhs lambdag@ walk walk* mzerog unitg
    choiceg lambdaf@ : take empty-f conde conda ifa
    condu ifu fresh project onceo succeed fail prt)

  (import (rnrs) (only (chezscheme) pretty-print))

(define var
  (lambda (x)
    (vector x)))

(define var?
  (lambda (x)
    (vector? x)))

(define rhs
  (lambda (x)
    (cdr x)))

(define lhs
  (lambda (x)
    (car x)))

(define-syntax :
  (lambda (x)
    (syntax-violation 'mk "misplaced aux keyword" x)))

(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (a : s c) e)
     (lambda (a) (let ((s (car a)) (c (cdr a))) e)))
    ((_ (a) e) (lambda (a) e))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define walk
  (lambda (v s)
    (cond
      ((var? v)
       (let ((a (assq v s)))
         (cond
           (a (walk (rhs a) s))
           (else v))))
      (else v))))

(define walk*
  (lambda (w s)
    (let ((v (walk w s)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons
           (walk* (car v) s)
           (walk* (cdr v) s)))
        (else v)))))

(define mzerog (lambda () #f))
(define unitg (lambdag@ (a) a))
(define choiceg (lambda (a f) (cons a f)))

(define succeed (lambdag@ (a) a))
(define fail (lambdag@ (a) (mzerog)))
(define prt (lambdag@ (a) (begin (pretty-print a) (unitg a))))

(define-syntax inc 
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ((a-inf e))
       (cond
         ((not a-inf) e0)
         ((procedure? a-inf)  (let ((f^ a-inf)) e1))
         ((not (and (pair? a-inf)
                    (procedure? (cdr a-inf))))
          (let ((a^ a-inf)) e2))
         (else (let ((a (car a-inf)) (f (cdr a-inf))) 
                 e3)))))))

(define empty-f (lambdaf@ () (mzerog)))

(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else (case-inf (f)
              (() '())
              ((f) (take n f))
              ((a) (cons a '()))
              ((a f) (cons a (take (and n (- n 1)) f))))))))

(define-syntax bindg*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bindg* (bindg e g0) g ...))))

(define bindg
  (lambda (a-inf g)
    (case-inf a-inf
      (() (mzerog))
      ((f) (inc (bindg (f) g)))
      ((a) (g a))
      ((a f) (mplusg (g a) (lambdaf@ () (bindg (f) g)))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a) 
       (inc 
         (mplusg* 
           (bindg* (g0 a) g ...)
           (bindg* (g1 a) g^ ...) ...))))))

(define-syntax mplusg*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...)
     (mplusg e0 
       (lambdaf@ () (mplusg* e ...))))))

(define mplusg
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (inc (mplusg (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (lambdaf@ () (mplusg (f) f^)))))))

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc
         (ifa ((g0 a) g ...)
           ((g1 a) g^ ...) ...))))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* a-inf g ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (a)
       (inc
         (ifu ((g0 a) g ...)
           ((g1 a) g^ ...) ...))))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzerog))
    ((_ (e g ...) b ...)
     (let loop ((a-inf e))
       (case-inf a-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((a) (bindg* a-inf g ...))
         ((a f) (bindg* (unitg a) g ...)))))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g ...)
     (lambdag@ (a)
       (inc
         (let ((x (var 'x)) ...)
           (bindg* (g0 a) g ...)))))))

(define-syntax project 
  (syntax-rules ()
    ((_ (x ...) g g* ...)  
     (lambdag@ (a : s c)
       (let ((x (walk* x s)) ...)
         ((fresh () g g* ...) a))))))

(define onceo (lambda (g) (condu (g))))

)

(import (mk))
