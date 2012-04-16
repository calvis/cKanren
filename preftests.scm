(library (cKanren preftests)
  (export run-preftests)
  (import
    (rnrs)
    (cKanren ck)
    (cKanren tree-unify)
    (cKanren pref)
    (cKanren tester))

  (define (run-preftests)

    (test-check "pref 1"
      (run* (q) (prefo q '(1 2 3)))
      `(1))
    (test-check "pref 2"
      (run* (q) (prefo q '(1 2 3)) (== q 3))
      `(3))
    (test-check "pref 3"
      (run* (q) (prefo q '(1 2 3)) (== q 4))
      `())
    )
  
  )
