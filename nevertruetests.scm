(library (cKanren nevertruetests)
  (export run-nevertruetests)
  (import
    (rnrs)
    (cKanren ck)
    (cKanren never-true)
    (cKanren tree-unify)
    (cKanren tester))

  (define (run-nevertruetests)

    (test-check "1"
      (run* (q) (== q '()) (never-pairo q))
      '(()))

    (test-check "2"
      (run* (q) (== q '(a . d)) (never-pairo q))
      '())

    (test-check "3"
      (run* (q) (== q 5) (never-trueo integer? q))
      '())

    (test-check "4"
      (run* (q) (== q 'x) (never-trueo integer? q))
      '(x))

    (test-check "5"
      (run* (q) (== q 'x) (allowedo symbol? q))
      '(x))

    (test-check "6"
      (run* (q) (== q 'x) (requiredo symbol? q))
      '(x))

    (test-check "7"
      (run* (q) (requiredo symbol? q))
      '())

    ;; Comment this out if your implementation does not support built
    ;; in procedure equivalence.
    (test-check "8"
      (run* (q) (allowedo symbol? q))
      `((_.0 : (allowed (,symbol? _.0))))))

  )

