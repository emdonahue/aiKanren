(library (dfs-tests)
  (export run-dfs-tests)
  (import (chezscheme) (test-runner) (aikanren) (utils))

  (define (run-dfs-tests)
    (tassert "dfs trivial" (run1*-dfs (x1) (== x1 1)) 1)
))
