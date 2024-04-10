(import (test-runner) (mk core mini-substitution) (mk core))

(define x1 (var 1))
(define x2 (var 2))
(define x3 (var 3))

(test-suite
 mini-substitution

 (tassert "miniwalk empty" (mini-walk '() x1) x1)
 (tassert "miniwalk bound-ground var" (mini-walk `((,x1 . 1)) x1) 1)
 (tassert "mini unify failure" (mini-unify '() '(1 . 2) '(2 . 2)) failure))
