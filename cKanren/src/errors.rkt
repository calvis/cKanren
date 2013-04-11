#lang racket

(provide (for-syntax build-srcloc build-srcloc-stx))
(provide format-source)

;; == ERROR CHECKING ===========================================================

(define cd (current-directory))

(define-for-syntax (build-srcloc stx)
  (srcloc
   (syntax-source stx)
   (syntax-line stx)
   (syntax-column stx)
   (syntax-position stx)
   (syntax-span stx)))

(define-for-syntax (build-srcloc-stx stx)
  #`(srcloc
     '#,(syntax-source stx)
     '#,(syntax-line stx)
     '#,(syntax-column stx)
     '#,(syntax-position stx)
     '#,(syntax-span stx)))

(define (format-source src)
  (define source (srcloc-source src))
  (cond
   [(path? source)
    (define absolute-path (path->string source))
    (define location (find-relative-path cd absolute-path))
    (define line (srcloc-line src))
    (define column (srcloc-column src))
    (string->symbol (format "~a:~s:~s" location line column))]
   [else #f]))

