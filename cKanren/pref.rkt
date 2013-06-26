#lang racket

;; prefo allows the user to assign a variable several acceptable
;; values without generating extra answers.
;;
;; It is possible to assign a "preference" list to a variable, where
;; the list is in order by preference.  For example,
;;
;; ... (prefo x '(1 2 3)) ...
;;
;; will unify x and 1 if the program reaches the end with x still
;; unground.  It is also acceptable if x is unified with any value
;; in the domain zbefore reification.
;;
;; This goal is not designed to be compatitble with =/= (from neq.scm)

(require "ck.rkt" "tree-unify.rkt")
(provide prefo enforce-constraintspref)

(define prefo
  (lambda (x l)
    (prefo-c x l)))

(define prefo-c
  (lambda (x l)
    (lambdam@ (a : s c)
      (let ((x (walk x s)))
        (cond
         ((var? x)
          ((update-c (build-oc prefo-c x l)) a))
         ((memq x l) a)
         (else mzerom))))))

(define pick-prefs
  (lambda ()
    (lambdam@ (a : s c)
      (bindm a
        (letrec
            ((loop
              (lambda (c^)
                (cond
                 ((null? c^) identitym)
                 (else
                  (let ((x (walk (caar c^) s)))
                    (cond
                     ((var? x)
                      (conj
                       (== x (cadar c^))
                       (loop (cdr c^))))
                     (else (loop (cdr c^))))))))))
          (loop
           (map
            (lambda (oc)
              (let ((p (oc-rands oc)))
                (cons (car p) (cadr p))))
            (filter/rator 'prefo-c c))))))))

(define enforce-constraintspref
  (lambda (x)
    (pick-prefs)))

(extend-enforce-fns 'pref enforce-constraintspref)

