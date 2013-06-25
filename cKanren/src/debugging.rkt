#lang racket/base

(require "helpers.rkt")

(provide (all-defined-out))

;; wrapper for the tree
(struct path (t)
  #:methods gen:custom-write
  [(define (write-proc . args) (apply write-path args))])

;; writes a path
(define (write-path path port mode)
  (let ([fn (lambda (s) ((parse-mode mode) s port))])
    (fn "#path[" )
    (unless (null? (path-t path)) (fn " "))
    (for ([br (reverse (path-t path))])
         (fn (format "~s " br)))
    (fn "]")))

;; an empty tree
(define empty-t (path '()))

;; adds a level to the tree with label l if it exists, a gensym otherwise
(define (add-level p l) 
  (cond
   [l (path (cons l (path-t p)))]
   [else (path (cons (gensym 'tr) (path-t p)))]))

