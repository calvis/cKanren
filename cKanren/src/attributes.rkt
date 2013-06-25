#lang racket/base

(require "helpers.rkt" "ocs.rkt" "constraint-store.rkt")

(provide (struct-out attr-oc)
         build-attr-oc get-attributes)

;; defines an attributed constraint (for attributed variables)
(struct attr-oc oc (type uw?) ;; for "unifies with?"
  #:extra-constructor-name make-attr-oc
  #:methods gen:custom-write
  [(define (write-proc attr-oc port mode)
     (define fn (lambda (str) ((parse-mode mode) str port)))
     (fn (format "#oc<~a ~s" (oc-rator attr-oc) (attr-oc-type attr-oc)))
     (for ([arg (oc-rands attr-oc)])
          (fn (format " ~a" arg)))
     (fn (format ">")))])

;; builds an attributed constraint
(define-syntax build-attr-oc
  (syntax-rules ()
    [(_ op x uw?)
     (let ((x^ x))
       (make-attr-oc (op x^) attr-tag `(,x^) 'op uw?))]))

;; gets the attributes of variable x in the constraint store
(define (get-attributes x c)
  (define (x-attr? oc) 
    (eq? (car (oc-rands oc)) x))
  (let ((attrs (filter x-attr? (filter/rator attr-tag c))))
    (and (not (null? attrs)) attrs)))

