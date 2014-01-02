#lang racket/base

;; This file provides the minimum core of cKanren functionalities

(require "macros.rkt")
(provide define-constraint-type transformer)

(provide define-constraint
         constraint
         add-constraint-event
         remove-constraint-event)

;; constraints
(require "constraints.rkt") 
(provide succeed fail transformer? #%app-safe)

;; debugging
(require "debugging.rkt") 

(require "events.rkt")
(provide define-event send-event)

;; framework
(require "framework.rkt") 
(provide add-association add-constraint constraint update-package run run*
         sort-by-lex<= lex<= define-constraint-interaction)
;; (provide (for-syntax search-strategy))

;; lex
(require "lex.rkt")
(provide sort-by-lex<= lex<=)

;; mk-structs
(require "mk-structs.rkt") 
(provide gen:mk-struct mk-struct? default-mk-struct? recur constructor 
         reify-mk-struct override-occurs-check? reify-term any/var? 
         any-relevant/var? walk* same-default-type?)

;; operators
(require "operators.rkt") 
(provide conj disj conde fresh fresh-aux)
(provide ifu condu ifa conda project onceo)
(provide debug debug-conde prt prtm prtt)
(provide for/disj for/conj)

;; package
(require "package.rkt") 
(provide empty-a make-a)
(provide occurs-check walk prefix-s ext-s ext-s*)
(provide empty-c ext-c remq-c filter/rator filter-memq/rator)

;; running
(require "running.rkt")
(provide run run* run/lazy define-constraint-interaction
         start/ir extend/ir enforce/ir reify/ir reifyc/ir exit/ir exitc/ir)

;; variables
(require "variables.rkt") 
(provide var var? var-x define-var-type define-cvar-type) 
