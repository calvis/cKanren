#lang racket

(require "../../unstable/ak.rkt")
(provide nnf prepare A E)

;; NNF taken from Oleg Kiselyov's translation of leanTAP
;; see http://kanren.sourceforge.net/
;; this adaptation positions noms in the right places

(define-syntax A
  (syntax-rules ()
    ((A var body) `(forall var ,(lambda (var) `body)))))

(define-syntax E
  (syntax-rules ()
    ((E var body) `(ex var ,(lambda (var) `body)))))

(define (show-formula fml)
  (cond
   ((not (pair? fml)) fml)
   ((eq? (car fml) 'var) fml)
   ((eq? (car fml) 'forall) (let ((var (cadr fml)))
                              `(A ,var ,(show-formula ((caddr fml) var)))))
   ((eq? (car fml) 'ex) (let ((var (cadr fml)))
                          `(E ,var ,(show-formula ((caddr fml) var)))))
   (else (cons (car fml) (map show-formula (cdr fml))))))

(define-syntax match-case-simple
  (syntax-rules ()
    ((_ exp clause ...)
     (let ((val-to-match exp))
       (match-case-simple* val-to-match clause ...)))))

(define (match-failure val)
  (error 'match-failure "failed match ~s" val))

(define-syntax match-case-simple*
  (syntax-rules (else)
    ((_ val (else exp ...))
     (let () exp ...))
    ((_ val)
     (match-failure val))
    ((_ val (pattern () exp ...) . clauses)
     (let ((fail (lambda () (match-case-simple* val . clauses))))
       ;; note that match-pattern may do binding. Here,
       ;; other clauses are outside of these binding
       (match-pattern val pattern (let () exp ...) (fail))))
    ((_ val (pattern guard exp ...) . clauses)
     (let ((fail (lambda () (match-case-simple* val . clauses))))
       (match-pattern val pattern
                      (if guard (let () exp ...) (fail))
                      (fail))))
    ))


;; (match-pattern val pattern kt kf)
(define-syntax match-pattern
  (syntax-rules (? quote unquote)
    ((_ val ? kt kf) kt)
    ((_ val () kt kf)
     (if (null? val) kt kf))
    ((_ val (quote lit) kt kf)
     (if (equal? val (quote lit)) kt kf))
    ((_ val (unquote var) kt kf)
     (let ((var val)) kt))
    ((_ val (x . y) kt kf)
     (if (pair? val)
         (let ((valx (car val))
               (valy (cdr val)))
           (match-pattern valx x
                          (match-pattern valy y kt kf)
                          kf))
         kf))
    ((_ val lit kt kf)
     (if (equal? val (quote lit)) kt kf))))

(define (nnf fml)
  (match-case-simple fml

                     ;; trivial re-writing using the standard tautologies
                     ((not (not ,a)) ()
                      (nnf  a))
                     ((not (forall ,var ,gfml)) ()
                      (nnf  `(ex ,var ,(lambda (x) `(not ,(gfml x))))))
                     ((not (ex ,var ,gfml)) ()
                      (nnf  `(forall ,var ,(lambda (x) `(not ,(gfml x))))))
                     ((not (and . ,fmls)) ()
                      (nnf  `(or ,@(map (lambda (x) `(not ,x)) fmls))))
                     ((not (or . ,fmls)) ()
                      (nnf  `(and ,@(map (lambda (x) `(not ,x)) fmls))))
                     ((=> ,a ,b) ()
                      (nnf  `(or (not ,a) ,b)))
                     ((not (=> ,a ,b)) ()
                      (nnf  `(and ,a (not ,b))))
                     ((<=> ,a ,b) ()
                      (nnf  `(or (and ,a ,b) (and (not ,a) (not ,b)))))
                     ((not (<=> ,a ,b)) ()
                      (nnf  `(or (and (not ,a) ,b) (and ,a (not ,b)))))

                     
                     ;; propagate inside
                     ((forall ,x ,gfml) ()
                      (let ((v (nom x)))
                        `(forall ,(tie v (nnf (gfml `(var ,v)))))))
                     ((and . ,fmls) ()
                      `(and ,@(map (lambda (x) (nnf  x)) fmls)))
                     ((or . ,fmls) ()
                      `(or ,@(map (lambda (x) (nnf  x)) fmls)))

                     ;; skolemization. See the paper
                     ((ex ,v ,gfml) ()
                      (let* ((fvars (rem-dups (fv (show-formula `(ex ,v ,gfml)))))
                             (fml-ex `(,(gensym) . ,fvars))
                             (fml-sk (gfml fml-ex)))
                        (nnf  fml-sk)))
                     ((ex ? ,gfml) ()
                      ;; replace quantified var with a constant. We use `sk' for clarity
                      (let* ((fml-ex `(sk ,(show-formula (gfml 'ex))))
                             (fml-sk (gfml fml-ex))) ;; replace qu. var. with skolem function
                        (nnf  fml-sk)))

                     ;; handle literals
                     ((not ,l) () `(lit (neg ,(handle-lit l))))
                     (else `(lit (pos ,(handle-lit fml))))))

(define handle-lit
  (lambda (lit)
    (match-case-simple lit
                       [(var ,x) (nom? x) `(var ,x)]
                       [,x (symbol? x) `(sym ,x)]
                       [(,f . ,d) (symbol? f) `(app ,f . ,(map handle-lit d))])))

(define fv
  (lambda (fml)
    (match-case-simple fml
                       [(var ,x) (nom? x) (list `(var ,x))]
                       [(not ,x) () (fv x)]
                       [(,op ,x ,y) (member op '(and or => <=>)) (append (fv x) (fv y))]
                       [(forall ,x ,t) () (remq x (fv t))]
                       [(exist ,x ,t) () (remq x (fv t))]
                       [(,f . ,args) () (apply append (map fvt args))]
                       [else '()])))

(define fvt
  (lambda (fml)
    (match-case-simple fml
                       [(var ,x) (nom? x) (list `(var ,x))]
                       [(,f . ,args) () (apply append (map fvt args))]
                       [else '()])))

(define rem-dups
  (lambda (ls)
    (cond
     [(null? ls) '()]
     [(member (car ls) (cdr ls)) (rem-dups (cdr ls))]
     [else (cons (car ls) (rem-dups (cdr ls)))])))


(define prepare
  (lambda (axioms theorem)
    (let* ((neg-formula (if (null? axioms)
                            `(not ,theorem)
                            (build-and (cons `(not ,theorem) axioms))))
           (nf (nnf neg-formula)))
      nf)))

(define build-and
  (lambda (ax)
    (cond
     [(null? ax) '()]
     [(null? (cdr ax)) (car ax)]
     [else `(and ,(car ax) ,(build-and (cdr ax)))])))


