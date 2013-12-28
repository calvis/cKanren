#lang racket

(require 
 (rename-in "../../unstable/ak.rkt" [nominal-== ==]) 
 "nnf.rkt"
 (only-in "../../ck.rkt" conde fresh project run))
(provide proveo do-prove-th A E)

;; substitution
(define subst
  (lambda (fml env out)
    (conde
     ((fresh (l r)
        (== `(pos ,l) fml)
        (== `(pos ,r) out)
        (subst-fmlo l env r)))
     ((fresh (l r)
        (== `(neg ,l) fml)
        (== `(neg ,r) out)
        (subst-fmlo l env r))))))

(define subst-fmlo
  (lambda (fml env out)
    (conde
     ((fresh (a)
        (== `(var ,a) fml)
        (lookupo a env out)))
     ((fresh (a)
        (== `(sym ,a) fml)
        (== fml out)))
     ((fresh (f d r)
        (== `(app ,f . ,d) fml)
        (== `(app ,f . ,r) out)
        (subst-tm* d env r))))))

(define subst-tm*
  (lambda (tm* env out)
    (conde
     ((== '() tm*) (== '() out))
     ((fresh (a d r1 r2)
        (== `(,a . ,d) tm*)
        (== `(,r1 . ,r2) out)
        (subst-fmlo a env r1)
        (subst-tm* d env r2))))))

(define lookupo
  (lambda (x env out)
    (fresh (a d va vd)
      (conde
       ((== `((,x . ,out) . ,d) env))
       ((== `(,a . ,d) env)
        (lookupo x d out))))))

(define negateo
  (lambda (fml neg)
    (fresh (lit)
      (conde
       ((== `(pos ,lit) fml)
        (== `(neg ,lit) neg))
       ((== `(neg ,lit) fml)
        (== `(pos ,lit) neg))))))


(define proveo
  (lambda (fml unexp lits env proof)
    (conde
     ((fresh (a b p1)
        (== `(and ,a ,b) fml)
        (== `(conj . ,p1) proof)
        (proveo a (cons b unexp) lits env p1)))
     ((fresh (a b p1 p2)
        (== `(or ,a ,b) fml)
        (== `(split ,p1 ,p2) proof)
        (proveo a unexp lits env p1)
        (proveo b unexp lits env p2)))
     ((fresh-nom (v)
                 (fresh (x1 b unexp1 p1)
                   (== `(forall ,(tie v b)) fml)
                   (== `(univ . ,p1) proof)
                   (appendo unexp (list fml) unexp1)
                   (proveo b unexp1 lits
                           `((,v . ,x1) . ,env) p1))))
     ((fresh (lit new-lit)
        (== `(lit ,lit) fml)
        (subst lit env new-lit)
        (conde
         ((fresh (l rest neg p1)
            (== `(,l . ,rest) lits)
            (== `(close) proof)
            (negateo new-lit neg)
            (membero neg lits)))
         ((fresh (next unexp1 p1)
            (== `(,next . ,unexp1) unexp)
            (== `(savefml . ,p1) proof)
            (proveo next unexp1
                    (cons new-lit lits) env p1)))))))))

(define membero
  (lambda (x ls)
    (conde
     ((fresh (d)
        (==-check `(,x . ,d) ls)))
     ((fresh (a d)
        (== `(,a . ,d) ls)
        (membero x d))))))

(define appendo
  (lambda (l1 l2 l3)
    (conde
     ((== '() l1) (== l2 l3))
     ((fresh (x l11 l31)
        (== l1 (cons x l11))
        (== l3 (cons x l31))
        (appendo l11 l2 l31))))))

(define (do-prove-th axioms theorem)
  (let* ((nf (prepare axioms theorem)))
    (let ((pr (run 1 (q) (proveo nf '() '() '() q))))
      (when (null? pr) (error 'prove "failure!"))
      (car pr))))



