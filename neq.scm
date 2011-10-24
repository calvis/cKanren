;; Copyright (C) 2011 by Claire E. Alvis, Jeremiah J. Willcock, Kyle M. Carter,
;; William E. Byrd, Daniel P. Friedman
;; 
;; Permission is hereby granted, free of charge, to any person obtaining a copy
;; of this software and associated documentation files (the "Software"), to deal
;; in the Software without restriction, including without limitation the rights
;; to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
;; copies of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;; 
;; The above copyright notice and this permission notice shall be included in
;; all copies or substantial portions of the Software.
;; 
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;; IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;; FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;; AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;; LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
;; THE SOFTWARE.


(library
  (neq)

  (export
    ;; goals
    =/=
    all-diffo
    useneq

    ;; for composition
    process-prefixneq
    enforce-constraintsneq
    reify-constraintsneq)

  (import
    (rnrs)
    (mk)
    (ck))

;;; little helpers

(define recover/vars
  (lambda (p)
    (cond
      ((null? p) '())
      (else
        (let ((x (lhs (car p)))
              (v (rhs (car p)))
              (r (recover/vars (cdr p))))
          (cond
            ((var? v) (ext/vars v (ext/vars x r)))
            (else (ext/vars x r))))))))

(define ext/vars
  (lambda (x r)
    (cond
      ((memq x r) r)
      (else (cons x r)))))

;;; serious functions

(define process-prefixneq
  (lambda (p c)
    (run-constraints (recover/vars p) c)))

(define oc->prefix
  (lambda (oc)
    (car (oc->rands oc))))

(define enforce-constraintsneq (lambda (x) unitg))

;; (define reify-constraintsneq
;;   (lambda (m r)
;;     (lambdag@ (a : s d c)
;;       (let* ((c (walk* c r))
;;              (p* (map oc->prefix c))
;;              (c (remp any/var? p*)))
;;         (cond
;;           ((null? c) m)
;;           (else `(,m : . ((=/= . ,c)))))))))

(define reify-constraintsneq
  (lambda (m r)
    (lambdag@ (a : s d c)
      (let* ((c (walk* c r))
             (p* (remp any/var? (map oc->prefix c))))
        (cond
          ((null? p*) m)
          (else `(,m : . ((=/= . ,p*)))))))))

(define =/=neq-c
  (lambda (p)
    (lambdam@ (a : s d c)
      (cond
        ((unify p s)
         =>
         (lambda (s^)
           (let ((p (prefix-s s s^)))
             (cond
               ((null? p) #f)
               (else ((normalize-store p) a))))))
        (else a)))))

(define normalize-store
  (lambda (p)
    (lambdam@ (a : s d c)
      (let loop ((c c) (c^ '()))
        (cond
          ((null? c)
           (let ((c^ (ext-c (build-oc =/=neq-c p) c^)))
             (make-a s d c^)))
          ((eq? (oc->rator (car c)) '=/=neq-c)
           (let* ((oc (car c))
                  (p^ (oc->prefix oc)))
             (cond
               ((subsumes? p^ p) a)
               ((subsumes? p p^) (loop (cdr c) c^))
               (else (loop (cdr c) (cons oc c^))))))
          (else (loop (cdr c) (cons (car c) c^))))))))

(define subsumes?
  (lambda (p s)
    (cond
      ((unify p s)
       => (lambda (s^) (eq? s s^)))
      (else #f))))

;;;-----------------------------------------------------------------

;;; goals

;; (define =/=
;;   (lambda (u v)
;;     (lambdag@ (a : s d c)
;;       (cond
;;         ((unify `((,u . ,v)) s)
;;          => (lambda (s^)
;;               ((=/=neq-c (prefix-s s s^)) a)))
;;         (else (unitg a))))))

(define =/=
  (lambda (u v)
    (goal-construct (=/=-c u v))))

(define =/=-c
  (lambda (u v)
    (lambdam@ (a : s d c)
      (cond
        ((unify `((,u . ,v)) s)
         => (lambda (s^)
              ((=/=neq-c (prefix-s s s^)) a)))
        (else a)))))

(define all-diffo
  (lambda (l)
    (conde
      ((== l '()))
      ((fresh (a) (== l `(,a))))
      ((fresh (a ad dd)
         (== l `(,a ,ad . ,dd))
         (=/= a ad)
         (all-diffo `(,a . ,dd))
         (all-diffo `(,ad . ,dd)))))))

;;; to use the =/= definitions, invoke (useneverequalo)

(define useneq
  (lambda ()
    (process-prefix process-prefixneq)
    (enforce-constraints enforce-constraintsneq)
    (reify-constraints reify-constraintsneq)))

)
