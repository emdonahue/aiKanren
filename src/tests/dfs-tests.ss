(library (dfs-tests)
  (export run-dfs)
  (import (chezscheme) (test-runner) (aikanren))

  (define (run-dfs-tests)
    (tassert "dfs trivial" (run1*-dfs (x1) (== x1 1)) 1)
))
