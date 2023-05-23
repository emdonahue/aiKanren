(library (mini-substitution-tests)
  (export run-mini-substitution-tests)
  (import (chezscheme) (test-runner) (mini-substitution) (datatypes))

  (define (run-mini-substitution-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))

    (tassert "miniwalk empty" (mini-walk '() x1) x1)
    (tassert "miniwalk bound-ground var" (mini-walk `((,x1 . 1)) x1) 1)
    
))
