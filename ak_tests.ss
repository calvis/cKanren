;;; And now the tests from the old alphamk.scm

(load "alphaK.ss")
(import (alphaK))

(define-syntax testit
  (syntax-rules ()
    ((_ exp val)
     (begin
       (display "testing: ")
       (tester 'exp exp val)))))

(define tester
  (lambda (exp v val)
    (cond
      ((equal? v val) (write 'okay) (newline))
      (else
        (error 'testit
               (format "exp: ~s\nexpected: ~s\ncomputed: ~s" exp val v))))))

(testit
 (run 1 (q) (fresh-var (x y z) (nom== x z) (nom== 3 y)))
 '(_.0))

(testit
 (run 1 (q) (fresh-var (x y) (nom== x q) (nom== 3 y)))
 '(_.0))

(testit
  (run 1 (y)
    (fresh-var (x z) 
      (nom== x z)
      (nom== 3 y)))
 '(3))

(testit
 (run 1 (q)
  (fresh-var (x z)
    (nom== x z)
    (nom== 3 z)
    (nom== q x)))
 '(3))

(testit
  (run 1 (y)
   (fresh-var (x y)
     (nom== 4 x)
     (nom== x y))
   (nom== 3 y))
  '(3))

(testit
  (run 1 (x) (nom== 4 3))
  '())

(testit
 (run 2 (q)
  (fresh-var (x y z)
    (conde
      ((nom== `(,x ,y ,z ,x) q))
      ((nom== `(,z ,y ,x ,z) q)))))
 '((_.0 _.1 _.2 _.0)
   (_.0 _.1 _.2 _.0)))

(testit
 (run 5 (q)
  (let loop ()
    (conde
      ((nom== #f q))
      ((nom== #t q))
      ((loop)))))
 '(#f #t #f #t #f))

(define anyo 
  (lambda (g)
    (conde
      (g)
      ((anyo g)))))

(testit
 (run 5 (q)
  (conde
    ((anyo (nom== #f q)))
    ((nom== #t q))))
 '(#t #f #f #f #f))

(testit
 (run 10 (q)
   (anyo 
    (conde
      ((nom== 1 q))
      ((nom== 2 q))
      ((nom== 3 q)))))
 '(1 2 3 1 2 3 1 2 3 1))

(testit
 (run 3 (q)
  (let ((nevero (anyo (nom== #f #t))))
    (conde
      ((nom== 1 q))
      (nevero)
      ((conde
         ((nom== 2 q))
         (nevero)
         ((nom== 3 q)))))))
 '(1 2 3))

(testit
  (run* (q) (fresh-nom (a) (nom== a a)))
  '(_.0))

(testit
 (run* (q) (fresh-nom (a) (nom== a 5)))
 '())

(testit
  (run* (q) (fresh-nom (a b) (nom== a b)))
  '())

(testit
  (run* (q) (fresh-nom (a b) (nom== b q)))
  '(a.0))

(testit
 (run* (q)
  (fresh-var (x y z)
    (fresh-nom (a)
      (nom== x a)
      (fresh-nom (a b)
        (nom== y a)
        (nom== `(,x ,y ,z ,a ,b) q)))))
  '((a.0 a.1 _.0 a.1 a.2)))

(testit
 (run* (q)
  (fresh-nom (a b)
    (nom== (tie a `(foo ,a 3 ,b)) q)))
 '((tie a.0 (foo a.0 3 a.1))))

(testit
  (run* (q) (fresh-nom (a b) (nom== `(foo ,a ,a) `(foo ,b ,b))))
  '())

(testit
  (run* (q) (fresh-nom (a b) (nom== (tie a a) (tie b b))))
  '(_.0))

(testit
 (run* (q) (fresh-nom (a b) (nom== (tie a q) (tie b b))))
 '(a.0))

(testit
 (run* (q)
  (fresh-var (t u)
    (fresh-nom (a b c d)
      (nom== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
      (nom== `(lam ,(tie c `(lam ,(tie d `(var ,c))))) u)
      (nom== t u))))
 '(_.0))

(testit
 (run* (q)
  (fresh-var (t u)
    (fresh-nom (a b c d)
      (nom== `(lam ,(tie a `(lam ,(tie b `(var ,a))))) t)
      (nom== `(lam ,(tie c `(lam ,(tie d `(var ,d))))) u)
      (nom== t u))))
 '())

(testit
 (run* (q) (fresh-nom (a) (hash a a)))
 '())

(testit
 (run* (q) (fresh-nom (a) (hash a 5)))
 '(_.0))

(testit
 (run* (q) (fresh-nom (a) (hash a (tie a a))))
 '(_.0))

(testit
 (run* (q) (fresh-nom (a b) (hash a (tie b a))))
 '())

(testit
 (run* (k)
  (fresh-var (t)
    (fresh-nom (a)
      (hash a k) 
      (nom== `(5 ,(tie a a) ,t) k))))
 '(((5 (tie a.0 a.0) _.0) : ((a.0 _.0)))))

(testit
 (run* (k)
  (fresh-var (t)
    (fresh-nom (a)
      (hash a k) 
      (nom== `(5 ,(tie a a) ,t) k)
      (nom== `(foo ,a 7) t))))
 '())

(testit
 (run* (k)
  (fresh-var (t)
    (fresh-nom (a b)
      (nom== (tie a (tie b t)) k) 
      (hash a t)
      (nom== `((,a ,b) ,b) t))))
 '())

(testit
 (run* (k)
  (fresh-var (t)
    (fresh-nom (a b)
      (nom== (tie a (tie b t)) k) 
      (hash a t)
      (nom== `(,b ,(tie a `(,a (,b ,b)))) t))))
 '((tie a.0 (tie a.1 (a.1 (tie a.0 (a.0 (a.1 a.1))))))))

(testit
 (run* (q)
  (fresh-var (k1 k2 t u)
    (fresh-nom (a b c d)
      (nom== (tie a (tie b t)) k1) 
      (hash a t)
      (nom== (tie c (tie d u)) k2)
      (hash c u)
      (nom== k1 k2)
      (nom== `(,k1 ,k2) q))))
 '((((tie a.0 (tie a.1 (sus ((a.1 . a.2) (a.0 . a.3)) _.0)))
     (tie a.3 (tie a.2 _.0)))
    :
    ((a.0 _.0) (a.3 _.0) (a.1 _.0)))))

(testit
 (run* (q)
  (fresh-var (k1 k2 t u)
    (fresh-nom (a b c d)
      (nom== (tie a (tie b t)) k1) 
      (hash a t)
      (nom== `(,b ,b) t)
      (nom== (tie c (tie d u)) k2)
      (hash c u)
      (nom== `(,d ,d) u)
      (nom== k1 k2)
      (nom== `(,k1 ,k2) q))))
 '(((tie a.0 (tie a.1 (a.1 a.1)))
    (tie a.2 (tie a.3 (a.3 a.3))))))

(testit
 (run* (q)
   (fresh-nom (a b)
     (fresh-var (x y)
       (nom== (tie a (tie a x)) (tie a (tie b y)))
       (nom== `(,x ,y) q))))
 '((((sus ((a.0 . a.1)) _.0) _.0) : ((a.0 _.0)))))

(testit 
 (run* (q)
  (fresh-nom (a b)
    (fresh-var (x y)
      (conde
        ((nom== (tie a (tie b `(,x ,b))) (tie b (tie a `(,a ,x)))))
        ((nom== (tie a (tie b `(,y ,b))) (tie b (tie a `(,a ,x)))))
        ((nom== (tie a (tie b `(,b ,y))) (tie b (tie a `(,a ,x)))))
        ((nom== (tie a (tie b `(,b ,y))) (tie a (tie a `(,a ,x))))))
      (nom== `(,x ,y) q))))
 '((a.0 a.1)
   (_.0 (sus ((a.0 . a.1)) _.0))
   ((_.0 (sus ((a.0 . a.1)) _.0)) : ((a.0 _.0)))))

(define substo  
  (lambda (e new a out)
    (conde
      ((nom== `(var ,a) e) (nom== new out))
      ((fresh-var (y)
         (nom== `(var ,y) e)
         (nom== `(var ,y) out)
         (hash a y)))
      ((fresh-var (rator ratorres rand randres)
         (nom== `(app ,rator ,rand) e)
         (nom== `(app ,ratorres ,randres) out)
         (substo rator new a ratorres)
         (substo rand new a randres)))
      ((fresh-var (body bodyres)
         (fresh-nom (c)
           (nom== `(lam ,(tie c body)) e)
           (nom== `(lam ,(tie c bodyres)) out)
           (hash c a)
           (hash c new)
           (substo body new a bodyres)))))))

(testit
 (run* (x)
  (fresh-nom (a b)
    (substo `(lam ,(tie a `(var ,b))) `(var ,a) b x)))
 '((lam (tie a.0 (var a.1)))))

(testit
 (run* (q)
  (fresh-nom (a b)
    (substo
      `(lam ,(tie a `(app (var ,a) (var ,b)))) b a q)))
 '((lam (tie a.0 (app (var a.0) (var a.1))))))


(define typo
  (lambda (g e te)
    (conde
      ((fresh-var (x)
         (nom== `(var ,x) e)
         (lookupo x te g)))
      ((fresh-var (rator trator rand trand)
         (nom== `(app ,rator ,rand) e)
         (nom== `(-> ,trand ,te) trator)
         (typo g rator trator)
         (typo g rand trand)))
      ((fresh-var (e^ te^ trand g^)
         (fresh-nom (b)
           (nom== `(lam ,(tie b e^)) e)
           (nom== `(-> ,trand ,te^) te)
           (hash b g)
           (nom== `((,b . ,trand) . ,g) g^)
           (typo g^ e^ te^))))
      ((fresh-var (rator t-val)
         (nom== `(C ,rator) e)
         (typo g rator `(-> (-> ,te ,t-val) ,t-val)))))))

(define !-c
  (lambda (gamma exp type)
    (fresh-var (m a b)
      (nom== `(c ,m) exp)
      (nom== a type)
      (!- gamma m `(-> (-> ,a ,b) ,b)))))

(define lookupo
  (lambda (x tx g)
    (fresh-var (a d)
      (nom== `(,a . ,d) g)
      (conde
        ((nom== `(,x . ,tx) a))
        ((fresh-var (x^ tx^)
           (nom== `(,x^ . ,tx^) a)
           (hash x x^)
           (lookupo x tx d)))))))

(testit
 (run* (q)
  (fresh-nom (c d)
    (typo '() `(lam ,(tie c `(lam ,(tie d `(var ,c))))) q)))
 '((-> _.0 (-> _.1 _.0))))

(testit
 (run* (q)
  (fresh-nom (c d)
    (typo '() `(lam ,(tie c `(lam ,(tie d `(var ,c))))) q)))
 '((-> _.0 (-> _.1 _.0))))

;; WEB 5 Feb 2012
;; diverges?
;; not sure what is up with this one
'(testit
(run* (q)
  (fresh-nom (c)
    (typo '() `(lam ,(tie c `(app (var ,c) (var ,c)))) q)))
 '())

(testit
 (run 5 (q) (typo '() q '(-> int int)))
 '((lam (tie a.0 (var a.0)))
   (C (lam (tie a.0 (var a.0))))
   (app (lam (tie a.0 (var a.0))) (lam (tie a.1 (var a.1))))
   (lam (tie a.0 (C (lam (tie a.1 (var a.1))))))
   (lam (tie a.0 (app (lam (tie a.1 (var a.1))) (var a.0))))))

(testit
 (run* (q)
  (fresh-var (x y z)
    (fresh-nom (a)      
      (hash a x)
      (nom== `(,y ,z) x)
      (nom== `(,x ,a) q))))
 '((((_.0 _.1) a.0) : ((a.0 _.0 _.1)))))
