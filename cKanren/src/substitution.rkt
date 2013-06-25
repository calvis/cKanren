#lang racket/base

(require "helpers.rkt" "variables.rkt")

(provide (all-defined-out))

;; == SUBSTITUTIONS ============================================================

;; wraps a substitution
(struct substitution (s)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-substitution args))])

;; writes a substitution
(define (write-substitution substitution port mode)
  (define fn (lambda (s) ((parse-mode mode) s port)))
  (define s (substitution-s substitution))
  (fn "#s[")
  (for ([p s])
    (fn " (") (fn (car p)) (fn " . ") (fn (cdr p)) (fn ")"))
  (unless (null? s) (fn " "))
  (fn "]"))

;; the empty association list, abbreviated s
(define empty-s '())

;; extends a substitution with a binding of x to v
(define (ext-s x v s)
  (cons `(,x . ,v) s))

(define (ext-s* p s)
  (append p s))

;; checks if x appears in v
(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or (occurs-check x (car v) s)
             (occurs-check x (cdr v) s)))
        (else #f)))))

;; returns the size of a substitution
(define size-s
  (lambda (s)
    (length s)))

;; walks an association list
(define (walk v s)
  (cond
   ((and (var? v) (assq v s))
    => (lambda (a) (walk (cdr a) s)))
   (else v)))

;; returns the part of s^ that is a prefix of s
(define (prefix-s s s^)
  (define (loop s^) 
    (cond
     [(eq? s^ s) '()] 
     [else (cons (car s^) (loop (cdr s^)))]))
  (if (null? s) s^ (loop s^)))

