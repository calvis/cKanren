#lang racket

(provide (all-defined-out))

;; sorts a list by lex<=
(define (sort-by-lex<= l) (sort l lex<=))

;; for pretty reification:
;; vector? <=
;; port?
;; procedure?
;; boolean?
;; null?
;; char?
;; number?
;; string?
;; symbol?
;; pair?
(define lex<=
  (lambda (x y)
    (cond
      ((vector? x) #t)
      ((vector? y) #f)
      ((port? x) #t)
      ((port? y) #f)
      ((procedure? x) #t)
      ((procedure? y) #f)
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((char? x)
       (cond
         ((char? y) (char<=? x y))
         (else #t)))
      ((char? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
      ((string? x)
       (cond
         ((string? y) (string<=? x y))
         (else #t)))
      ((string? y) #f)
      ((symbol? x)
       (cond
         ((symbol? y)
          (string<=? (symbol->string x)
                     (symbol->string y)))
         (else #t)))
      ((symbol? y) #f)
      ((pair? x)
       (cond
         ((pair? y)
          (cond          
            ((equal? (car x) (car y))
             (lex<= (cdr x) (cdr y)))
            (else (lex<= (car x) (car y)))))))
      ((pair? y) #f)
      (else #t))))

(define (insert-in-lex-order x ls)
  (cond
   [(null? ls) (list x)]
   [(lex<= x (car ls)) (cons x ls)]
   [else (cons (car ls) (insert-in-lex-order x (cdr ls)))]))



