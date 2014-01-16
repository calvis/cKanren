#lang racket

;; Based on code provided by Jason Hemann and Dan Friedman
;; See: https://github.com/jasonhemann/miniKanren

(require "ck.rkt" "src/helpers.rkt" "src/events.rkt" "src/framework.rkt"
         "src/constraints.rkt" "src/constraint-store.rkt" "src/macros.rkt")
(require (for-syntax racket/syntax syntax/parse "src/framework.rkt"))

(provide (all-defined-out))

(define-constraint-type attribute-constraint walk*)

(define attributes-uw? 
  (make-parameter '()))
(define extend-attributes-uw? 
  (extend-parameter attributes-uw?))

;; returns #t if attributes are ok
(define (check-attributes u v s c e)
  (let ([uattr (get-attributes u c e)]
        [vattr (get-attributes v c e)])
    ;; four possibilities: 
    ;; 1. u and v both have attributes
    ;; 2, 3. either u or v does not have attributes
    ;; 4. neither u nor v has attributes

    ;; (printf "check-attributes: ~a ~a ~a ~a\n" u uattr v vattr)
    (and (or (not uattr) (no-conflicts? uattr v vattr))
         (or (not vattr) (no-conflicts? vattr u uattr)))))

(define (get-attributes x c e)
  (define ocs (filter-something/rator attribute-constraint? c))
  (define events (filter (match-lambda 
                           [(add-attribute-constraint-event rator (list y))
                            (eq? x y)]
                           [else #f])
                         e))
  (append (filter-map (match-lambda [(oc rator (list y)) (and (eq? x y) rator)]) ocs)
          (map (match-lambda [(constraint-event rator rands) rator]) events)))

;; [List-of Rator] Value [List-of Rator] -> Boolean
(define (no-conflicts? vattr u uattr)
  (andmap (lambda (rator) ((attr-oc-uw? rator) u uattr)) vattr))

;; AtributeConstraintRator -> Boolean
(define (attr-oc-uw? rator)
  (cdr (assq rator (attributes-uw?))))

(define-syntax (define-attribute stx)
  (syntax-parse stx 
    [(define-attribute name
       (~or (~once (~seq #:satisfied-when pred?:id))
            (~optional (~seq #:incompatible-attributes (inc-attrs ...))
                       #:defaults ([(inc-attrs 1) '()]))
            (~optional (~seq #:causes (cause-attrs ...))
                       #:defaults ([(cause-attrs 1) '()])))
       ...)
     (define/with-syntax (name-fail-incompatible ...)
       (map (lambda (incompat)
              (format-id #'name "~a-~a-fail" 
                         (syntax-e #'name) 
                         (syntax-e incompat)))
            (syntax-e #'(inc-attrs ...))))
     (define/with-syntax name-unique
       (format-id #'name "~a-unique" (syntax-e #'name)))
     #'(begin
         (define-attribute-constraint (name x)
           #:package (a [s c e])
           #:reified
           (define body
             (cond
              [(var? x) 
               (add-constraint (name x))]
              [(pred? x) succeed]
              [else fail]))
           (cond
            [(empty-event? e)
             (conj (cause-attrs x) ... body)]
            [else body]))
         (define-constraint-interaction
           name-fail-incompatible
           [(name x) (inc-attrs x)] => [fail])
         ...
         (define-constraint-interaction
           name-unique
           [(name x) (name x)] => [(name x)])
         ;; (printf "~a: ~a\n" 'name x)

         ;; Value [List-of Attribute] -> Boolean
         (define (symbol-unifies-with? x attrs)
           (define incompatible  (list inc-attrs ...))
           (define incompatible? (curryr memq incompatible))
           (cond
            [(var? x)
             (or (not attrs) 
                 (andmap (compose not incompatible?) attrs))]
            [else (pred? x)]))
         (extend-attributes-uw? name symbol-unifies-with?))]))

(define-attribute symbol
  #:satisfied-when symbol?
  #:incompatible-attributes (number string))

(define-attribute number
  #:satisfied-when number?
  #:incompatible-attributes (symbol string))

(define-attribute string
  #:satisfied-when string?
  #:incompatible-attributes (number symbol))

