#lang racket

(require (for-syntax syntax/parse racket/syntax "syntax-classes.rkt")
         "syntax-classes.rkt"
         "constraints.rkt")

(provide (struct-out trigger)
         define-trigger)

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

