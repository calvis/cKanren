#lang racket

(require (for-syntax syntax/parse racket/syntax))

(provide (all-defined-out))
(provide (for-syntax (all-defined-out)))

(define (identity-update-fn x . rest) x)

(begin-for-syntax

 (define-splicing-syntax-class package-keyword
   #:attributes (package)
   (pattern (~seq #:package (a:id [s:id c:id e:id]))
            #:with package #'(a [s c e]))
   (pattern (~seq #:package a:id)
            #:with (s c e) (generate-temporaries #'(?s ?c ?e))
            #:with package #'(a [s c e]))
   (pattern (~seq)
            #:with (a s c e) (generate-temporaries #'(?a ?s ?c ?e))
            #:with package #'(a [s c e])))

 (define-syntax-class (argument default-fn)
   #:attributes (arg fn)
   (pattern [arg:id #:constant] 
            #:with fn #'identity-update-fn)
   (pattern [arg:id fn])
   (pattern arg:id
            #:with fn default-fn))

 ;; constructor keyword matching
 (define-splicing-syntax-class constructor-keyword
   #:attributes (constructor)
   (pattern (~seq #:constructor constructor:id))
   (pattern (~seq) #:with constructor (generate-temporary #'?constfn)))

 (define-splicing-syntax-class persistent-keyword
   #:attributes (persistent?)
   (pattern (~seq (~and #:persistent persistent?:keyword)))
   (pattern (~seq) #:with persistent? #'#f))

 (define-splicing-syntax-class reification-keyword
   #:attributes (reified)
   (pattern (~seq #:reified)
            #:with reified #'#t)
   (pattern (~seq #:reification-function _reify-expr:expr)
            #:with reified #'(#f _reify-expr))
   (pattern (~seq #:reify reify-expr:expr)
            #:with reified #'(#t reify-expr))
   (pattern (~seq) #:with reified #'#f))

 (define-splicing-syntax-class unique-keyword
   #:attributes (unique)
   (pattern (~seq #:unique)
            #:with unique #'#t)
   (pattern (~seq) #:with unique #'#f))

)
