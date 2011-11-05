;; To trace changes in the constraint and domain stores, replace
;; rem/run in ck with the following definition.  It will print the
;; stores (with all shadowed domains removed) before running a
;; constraint in the store.

(define smaller
  (lambda (d seen)
    (cond
      ((null? d) '())
      ((memq (caar d) seen) (smaller (cdr d) seen))
      (else
        (cons (car d) (smaller (cdr d) (cons (caar d) seen)))))))

(define rem/run   ;;; For tracing.
  (lambda (oc)
    (lambdam@ (a : s d c)
      (begin
        (write (smaller d '()))
        (newline)
        (write (smaller c '()))
        (newline)
        (newline)
        (cond
          ((memq oc c)
           (let ((c^ (remq oc c)))
             ((oc->proc oc) (make-a s d c^))))
          (else a))))))

