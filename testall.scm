(import
  (cKanren fdtests)
  (cKanren neqtests)
  (cKanren comptests)
  (cKanren nevertruetests)
  (cKanren preftests))

(run-fdtests)
(run-neqtests)
(run-comptests)
(run-nevertruetests)
(run-preftests)

