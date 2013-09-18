#lang racket

(require "helpers.rkt" "variables.rkt" "events.rkt")

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
(define (occurs-check x v^ s)
  (define v (walk/internal v^ s))
  (cond
   [(var? v) (eq? v x)]
   [(pair? v) 
    (or (occurs-check x (car v) s)
        (occurs-check x (cdr v) s))]
   [else #f]))

;; returns the size of a substitution
(define (size-s s) (length s))

(define (walk/internal v s)
  (cond
   [(and (var? v) (assq v s))
    => (lambda (a) (walk/internal (cdr a) s))]
   [else v]))

;; returns the part of s^ that is a prefix of s
(define (prefix-s s s^)
  (define (loop s^) 
    (cond
     [(eq? s^ s) '()] 
     [else (cons (car s^) (loop (cdr s^)))]))
  (if (null? s) s^ (loop s^)))

(define walk
  (case-lambda
   [(u s)
    (walk/internal u s)]
   [(u s c e)
    (cond
     [(not (var? u)) u]
     [(cond
       [(findf (curryr relevant? u) e)
        => (curry walk/shortcut u)]
       [else #f])]
     [else (walk/internal u s)])]))

(module+ test
  (require (prefix-in ru: rackunit))

  (ru:check-equal?
   (let ([u (var 'u)])
     (walk u '() #f
           (running-event
            (add-association-event u 'a)
            (build-chain-event
             (add-substitution-prefix-event '())
             (empty-event)
             (composite-event
              (list (add-substitution-prefix-event `((,u . b)))))))))
   'a)

  (ru:check-equal?
   (let ([u (var 'u)])
     (walk u '() #f
           (running-event
            (add-substitution-prefix-event `((,u . a)))
            (build-chain-event
             (add-substitution-prefix-event '())
             (empty-event)
             (composite-event
              (list (add-substitution-prefix-event `((,u . b)))))))))
   'a)

  (ru:check-equal?
   (let ([u (var 'u)])
     (walk u '() #f
           (running-event
            (add-substitution-prefix-event `())
            (build-chain-event
             (add-substitution-prefix-event '())
             (empty-event)
             (composite-event
              (list (add-substitution-prefix-event `((,u . b)))))))))
   'b))
