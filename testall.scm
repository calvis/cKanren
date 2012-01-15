(import 
  (cKanren fdtests)
  (cKanren neqtests) 
  (cKanren comptests))

(neq-test-all)
(fd-test-all)
(comp-test-all)
