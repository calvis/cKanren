#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "tree-unify.rkt" "neq.rkt" "src/helpers.rkt")
(require (for-syntax racket/syntax syntax/parse))

;; attributes
(provide define-attribute)

;; constraints
(provide eveno oddo symbolo numbero symbol-constrained? number-constrained?)

(define attributes (make-parameter '()))
(define (extend-attributes new-attr)
  (attributes (cons new-attr (attributes))))

(define-syntax (define-attribute stx)
  (syntax-parse stx 
    [(define-attribute name 
       (~seq #:satisfied-when pred?:expr)
       (~or (~optional (~seq #:reify-name reify-name)
                       #:defaults ([reify-name #'name]))
            (~optional (~seq #:incompatible-attributes (inc-attrs ...))
                       #:defaults ([(inc-attrs 1) '()])))
       ...)
     (with-syntax
       ([(nameo name-constrained? name-attr? reify-nameos)
         (map (lambda (str) (format-id #'name str (syntax-e #'name)))
              (list "~ao" "~a-constrained?" "~a-attr?" "reify-~aos"))])
       #'(begin
           (define (nameo u)
             (define incompatible `(inc-attrs ...))
             (define (check-inc-attrs u attrs)
               (and attrs
                    (ormap (lambda (aoc) 
                             (memq (attr-oc-type aoc) incompatible))
                           attrs)))
             (define (unifies-with? x attrs)
               (cond
                [(var? x) 
                 (not (check-inc-attrs x attrs))]
                [else (pred? x)]))
             (constraint
              #:package (a : s c)
              (let ([u (walk u s)])
                (cond
                 [(var? u)
                  (cond
                   [(check-inc-attrs u (get-attributes u c)) fail]
                   [else (update-c (build-attr-oc nameo u unifies-with?))])]
                 [(pred? u) succeed]
                 [else fail]))))
           (define (name-constrained? v attrs)
             (findf name-attr? attrs))
           (define (name-attr? oc)
             (eq? (attr-oc-type oc) 'nameo))
           (define reify-nameos
             (default-reify-attr 'reify-name 'nameo
               (lambda (x* r) (remove-duplicates x*))))
           (extend-attributes 'nameo)
           (extend-reify-fns 'nameo reify-nameos)))]))

(define-attribute symbol
  #:satisfied-when symbol?
  #:incompatible-attributes (numbero)
  #:reify-name sym)

(define-attribute number
  #:satisfied-when number?
  #:incompatible-attributes (symbolo)
  #:reify-name num)

(define remove-duplicates
  (lambda (l)
    (for/fold ([s '()])
              ([x l])
      (if (member x s) s (cons x s)))))

(define (rerun-type-cs x)
  (constraint
   #:package (a : s c)
   (let ([ocs (filter (lambda (oc) (memq (attr-oc-type oc) (attributes)))
                      (filter/rator attr-tag c))])
     (run-relevant-constraints (map (compose car oc-rands) ocs) c))))

;; etc

(define booleano
  (lambda (x)
    (conde
      ((== #f x) succeed)
      ((== #t x) succeed))))
         
(define-attribute even
  #:satisfied-when 
  (lambda (x) (and (integer? x) (even? x)))
  #:incompatible-attributes (oddo))

(define-attribute odd
  #:satisfied-when
  (lambda (x) (and (integer? x) (odd? x)))
  #:incompatible-attributes (eveno))

;; ckanren stuffs

(extend-enforce-fns attr-tag rerun-type-cs)


