#lang racket

(require (only-in "variables.rkt" cvar? var?)
         (only-in "events.rkt" relevant? findf walk/shortcut))

;; == SUBSTITUTIONS ============================================================
;;
;; A Substitution is a [List-of Association]
;; An Association is a (cons Var Value) 
;; A SubstitutionPrefix is Subsitution

(provide
 ;; Value -> Boolean
 ;; returns #t iff the value is a Subsitution
 substitution?

 ;; Substitution
 ;; the empty subsitution
 empty-s

 ;; Var Value Subsitution -> Subsitution
 ;; extends the given subsitution with a binding (cons Var Value)
 ext-s

 ;; SubsitutionPrefix Subsitution -> Subsitution
 ;; appends the associations in the prefix onto the given subsitution
 ext-s* 

 ;; Subsitution -> Number
 ;; returns the size of the substitution
 size-s

 ;; Substitution Substitution -> Substitution
 ;; returns the prefix of the first substitution that is not contained
 ;; in the second subsitution (it is an error to send two completely
 ;; unrelated substitutions)
 prefix-s

 ;; Var Value Subsitution -> Value
 ;; checks if the variable appears in the value (given the associations
 ;; in the substitution)
 occurs-check

 ;; Var Substitution -> Value
 ;; Var Substitution ConstraintStore Event -> Value
 ;; returns the association for the variable in the substitution or in 
 ;; the event (when given), or returns the variable unchanged if it has
 ;; no association
 walk

 ;; Var Substitution -> Value
 ;; returns the association for the variable in the substitution or
 ;; returns the variable unchanged if it has no association
 walk/internal
 )

(define substitution? list?)

;; the empty association list, abbreviated s
(define empty-s '())
(define empty-s? null?)

(define (ext-s x v s) (cons `(,x . ,v) s))
(define (ext-s* p s) (append p s))

(define (size-s s) (length s))

(define (prefix-s s s^)
  (define (loop s^) 
    (cond
     [(eq? s^ s) '()] 
     [else (cons (car s^) (loop (cdr s^)))]))
  (if (empty-s? s) s^ (loop s^)))

(define (occurs-check x v^ s)
  (define v (walk/internal v^ s #f))
  (cond
   [(var? v) (eq? v x)]
   [(pair? v) 
    (or (occurs-check x (car v) s)
        (occurs-check x (cdr v) s))]
   [else #f]))

(define walk
  (case-lambda
   [(u s)
    (walk/internal u s #f)]
   [(u s c e)
    (walk/internal u s e)]))

(define (walk/internal v s e)
  (cond
   [(and (cvar? v) (assq v s))
    => (lambda (a) (walk/internal (cdr a) s e))]
   [(and (cvar? v) e (findf (curry relevant? v) e))
    => (lambda (e^) (walk/internal (walk/shortcut v e^) s e))]
   [else v]))
