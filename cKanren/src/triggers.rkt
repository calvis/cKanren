#lang racket

(require (for-syntax syntax/parse racket/syntax "syntax-classes.rkt")
         "syntax-classes.rkt"
         "constraints.rkt"
         "events.rkt"
         "mk-structs.rkt")

(require (rename-in (only-in racket filter) [filter ls:filter]))

(provide (struct-out trigger)
         define-trigger)

;; some predefined triggers
(provide enter-scope
         leave-scope
         any-association-event
         any-enforce)

(struct trigger (subs interp))

;; TODO, weird scope of package (should be an error to try to use it
;; in event-names)
(define-syntax (define-trigger stx)
  (syntax-parse stx
    [(define-trigger (name args ...)
       (~seq (~or (~once pkgkw:package-keyword))
             ...)
       [(event-name:id event-arg ...)
        (~optional ((~literal =>) abort)
                   #:defaults ([abort (generate-temporary #'?abort)]))
        answer answer* ...]
       ...)
     (define/with-syntax (a [s c e]) #'pkgkw.package)
     (define/with-syntax subs
       #'(match-lambda [(struct event-name _) #t] ... [_ #f]))
     (define/with-syntax interp
       #'(lambda (args ...)
           (lambda@ (a [s c q t e]) 
             (match-lambda
               [(event-name event-arg ...)
                (=> abort)
                (let ([result (let () answer answer* ...)])
                  (list result))]
               ...
               [_ #f]))))
     #'(define name (trigger subs interp))]))

(define-trigger (enter-scope x)
  [(enter-scope-event y)
   (=> abort) (unless (or (not x) (eq? x y)) (abort)) y])

(define-trigger (leave-scope x)
  [(leave-scope-event y)
   (=> abort) (unless (or (not x) (eq? x y)) (abort)) y])

(define-trigger (any-association-event x)
  [(add-substitution-prefix-event p)
   (=> abort)
   (define (assoc-contains-var? u/v)
     (or (eq? x (car u/v)) (memq x (filter*/var? (cdr u/v)))))
   (cond
    [(ls:filter assoc-contains-var? p)
     => (lambda (p) (when (null? p) (abort)) p)]
    [else (abort)])])

(define-trigger (any-enforce ls)
  [(enforce-in-event ls^)
   (=> abort)
   (unless (ormap (curryr memq ls) ls^) (abort))]
  [(enforce-out-event ls^)
   (=> abort)
   (when (ormap (curryr memq ls) ls^) (abort))])
