#lang racket

(require "helpers.rkt" "package.rkt" "ocs.rkt" "constraint-store.rkt"
         "constraints.rkt" "operators.rkt")
(require (for-syntax syntax/parse racket/syntax))

(provide (all-defined-out))

(define constraint-interactions
  (make-parameter '()))

(define extend-constraint-interactions
  (extend-parameter constraint-interactions))

#;
(define-constraint-interaction
  same-template
  [(template ,x ,y ,env-var) (template ,x ,z ,env-var)]
  [#t ((== y z)
       (template x y env-var))])

(define-syntax (define-constraint-interaction stx)
  (syntax-parse stx 
    [(define-constraint-interaction 
       name:id
       (constraint-exprs ...)
       (~or (~optional (~seq #:package (a:id : s:id c:id))))
       ...
       clauses ...)
     (define a-name (or (attribute a) (generate-temporary #'?a)))
     (define s-name (or (attribute s) (generate-temporary #'?s)))
     (define c-name (or (attribute c) (generate-temporary #'?c)))
     (with-syntax*
       ([(a s c) (list a-name s-name c-name)]
        [constraint-interaction-expr
         #`(parse-constraint-interaction
            name (constraint-exprs ...) (clauses ...)
            (a s c))])
       #'(extend-constraint-interactions
          'name constraint-interaction-expr))]))

(define-syntax (parse-constraint-interaction stx)
  (syntax-parse stx
    [(parse-constraint-interaction 
      name
      ((rator rands ...) ...)
      ([pred? (constraints ...)] ...)
      (a s c))
     (with-syntax 
       ([(arg ...) (generate-temporaries #'(rator ...))])
       #`(let ()
           (define (run-interaction . arg*)
             (match (map oc-rands arg*)
               [`((rands ...) ...)
                (lambdam@/private (a : ?s ?c ?q ?t)
                  (let ([s (substitution-s ?s)]
                        [c (constraint-store-c ?c)])
                    (cond
                     [pred? 
                      (let ([new-c (remq*-c arg* c)])
                        (let ([new-a (make-a ?s (constraint-store new-c) ?q ?t)])
                          (bindm new-a (conj constraints ...))))]
                     ...
                     [else mzerom])))]
               ;; when the rators are all correct but the pattern
               ;; is more strict than we were expecting, we should
               ;; fail instead of erroring
               [_ mzerom]))
           (define (name oc)
             (let ([this-rator (oc-rator oc)])
               (generate-cond run-interaction oc c this-rator 
                              () ((rator rands ...) ...))))
           name))]))

(define-syntax (generate-cond stx)
  (syntax-parse stx 
    [(generate-cond run-interaction oc c this-rator (pattern ...) ()) #'fail]
    [(generate-cond 
      run-interaction oc c this-rator
      ((rator-pre rand-pre ...) ...)
      ((rator rand ...) (rator-post rand-post ...) ...))
     (with-syntax
      ([(pre ...)  (generate-temporaries #'(rator-pre ...))]
       [(post ...) (generate-temporaries #'(rator-post ...))]
       [(pre-ocs ...)  #'((filter/rator 'rator-pre c) ...)]
       [(post-ocs ...) #'((filter/rator 'rator-post c) ...)]
       [pattern-applies? #'(eq? 'rator this-rator)])
      (with-syntax
        ([run-rule
          #'(lambdam@ (a : s c)
              (bindm a
                (for*/fold
                 ([fn fail])
                 ([pre    pre-ocs] ...
                  [this (list oc)]
                  [post  post-ocs] ...)
                 (conda
                  [(run-interaction pre ... this post ...)]
                  [fn]))))]
         [rest-formatted 
          #'(generate-cond 
             run-interaction oc c this-rator
             ((rator-pre rand-pre ...) ... (rator rand ...))
             ((rator-post rand-post ...) ...))])
        #'(cond
           [pattern-applies?
            (conda
             [run-rule]
             [rest-formatted])]
           [else rest-formatted])))]))
