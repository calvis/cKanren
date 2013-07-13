#lang racket/base

;; This file provides the minimum core of cKanren functionalities

;; attributed variables
(require "attributes.rkt") 
(provide (struct-out attr-oc) build-attr-oc get-attributes default-reify-attr)

;; constraint interactions
(require "constraint-interactions.rkt") 
(provide define-constraint-interaction)

;; constraints
(require "constraints.rkt") 
(provide succeed fail identitym mzerom lambdam@)

;; debugging
(require "debugging.rkt") 

;; framework
(require "framework.rkt") 
(provide update-s replace-s reify-cvar update-c-nocheck
         update-package sort-by-lex<= lex<= default-reify bindm update-c
         extend-reify-fns run-relevant-constraints extend-enforce-fns
         define-lazy-goal reify-with-colon run run* run/lazy #%app-safe
         use-constraints trace-define constraint define-reified-constraint
         define-constraint)
(provide (for-syntax search-strategy))

;; mk-structs
(require "mk-structs.rkt") 
(provide gen:mk-struct mk-struct? default-mk-struct? recur constructor 
         reify-mk-struct override-occurs-check? reify-term any/var? 
         any-relevant/var? walk* same-default-type?)

;; ocs
(require "ocs.rkt") 
(provide (struct-out oc) build-oc)

;; operators
(require "operators.rkt") 
(provide conj conde fresh fresh-aux)
(provide ifu condu ifa conda project onceo)
(provide debug debug-conde prt prtm prtt)

;; package
(require "package.rkt") 
(provide empty-a make-a)
(provide occurs-check walk prefix-s ext-s ext-s*)
(provide empty-c ext-c ext-c* memq-c remq-c remq*-c replace-ocs c->list
         filter/rator filter-not/rator filter-memq/rator filter-not-memq/rator)

;; variables
(require "variables.rkt") 
(provide (struct-out var) define-var-type) 
