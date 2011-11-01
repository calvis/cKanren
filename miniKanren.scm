;; In order to use "basic" miniKanren

(load "mk.scm")
(load "ck.scm")

(import (mk))
(import (ck))

(process-prefix (lambda (p c) identitym))
(enforce-constraints (lambda (x) unitg))
(reify-constraints (lambda (m r) unitg))

