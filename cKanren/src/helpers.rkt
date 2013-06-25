#lang racket/base

(require (for-syntax racket/base))

(provide debug? parse-mode attr-tag extend-parameter)
(provide (for-syntax expand-debug?))

(begin-for-syntax
 (define expand-debug? (make-parameter #f)))

;; when debug?ging is turned on, print out the path as well
(define debug? (make-parameter #f))

;; parses the input to a write-proc
(define (parse-mode mode)
  (case mode [(#t) display] [(#f) display] [else display]))

(define attr-tag 'attr)

(define ((extend-parameter param) tag fn)
  (let ((fns (param)))
    (and (not (assq tag fns))
         (param (cons `(,tag . ,fn) fns)))))

