;; Example:
;; (print-gensym #f)
;; (pretty-print (expand '(matche '(1 2 3) ((,a ,b ,c) 1) ((,x d ,y) 2) (5) (,w) ((a b c)))))
;; (print-gensym #t)

(define-syntax lambdae
  (syntax-rules ()
    ((_ (x ...) c c* ...)
     (lambda (x ...) (matche (list x ...) (c c* ...))))))

(define-syntax fresh* ;;; easy way to deal with duplicate vars (as if fresh used let*)
  (syntax-rules ()
    ((_ () g ...) (fresh () g ...))  ;;; just in case there were no vars in pattern.
    ((_ (x) g ...) (fresh (x) g ...)) ;;; exactly one var
    ((_ (y x z ...) g ...) (fresh (y) (fresh* (x z ...) g ...))))) ;;; more than one.

(define-syntax matche
  (syntax-rules ()

    ((_ (f x ...) g* . cs)
     (let ((v (f x ...))) ;;; evaluate first argument once.
       (matche v g* . cs))) 

    ((_ v (pat g ...) ...) ;;; pass to driver list of uns and (empty) list of dones.
     (mpat0 ((pat (fresh* () (== `pat v) g ...)) ...) ()))))

(define-syntax mpat0  ;;; body is alwasys (fresh* (x ...) g ...)
  (syntax-rules ()
    
    ((_ () (done ...)) (conde done ...))  ;;; all done (no more undone)
    
    ((_ ((pat body) un* ...) done*) (mpat pat () body (un* ...) done*)))) ;;; do one un.

(define-syntax mpat ;;; virtually the same reasoning as earlier versions.
  (syntax-rules (unquote fresh*)

    ((_ (unquote x) () (fresh* (y ...) g ...) un* (done ...))
     (mpat0 un* (done ... ((fresh* (y ... x) g ...))))) ;;; empty stack. add var; one un done.
                                                        ;;; turn g to clause.
    
    ((_ (unquote x) (top stack ...) (fresh* (y ...) g ...) un* done*) 
     (mpat top (stack ...) (fresh* (y ... x) g ...) un* done*)) ;;; pop; add var
    
    ((_ (a . d) (top ...) body un* done*) (mpat a (d top ...) body un* done*)) ;;; push d
    
    ((_ ignore () body un* (done ...)) (mpat0 un* (done ... (body)))) ;;; empty stack
                                                                      ;;; turn g to clause.
    
    ((_ ignore (top stack ...) body un* done*) (mpat top (stack ...) body un* done*)))) ; pop














