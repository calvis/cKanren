(library
  (fdneq)

  (export
    =/=
    usefdneq)

  (import
    (rnrs)
    (mk)
    (ck)
    (only (fd)
      process-prefixfd
      enforce-constraintsfd
      =/=fd)
    (only (neq) 
      reify-constraintsneq)
    (rename (neq) (=/= =/=neq)))

  ;; goals

  (define =/=
    (lambda (u v)
      (project (u v)
        (cond
          ((and (integer? u) (integer? v)) (=/=fd u v))
          (else (=/=neq u v))))))

  ;; to use the combined definitions, envoke (usefdneq)

  (define usefdneq
    (lambda ()
      (process-prefix process-prefixfd)
      (enforce-constraints enforce-constraintsfd)
      (reify-constraints reify-constraintsneq)))

  )

