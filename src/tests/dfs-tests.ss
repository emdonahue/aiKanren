(library (dfs-tests)
  (export run-dfs-tests)
  (import (chezscheme) (test-runner) (aikanren) (utils))

  (define (run-dfs-tests)
    (tassert "dfs ==" (run1*-dfs (x1) (== x1 1)) 1)
    (tassert "dfs == & ==" (run1*-dfs (x1 x2) (== x1 1) (== x2 2)) '(1 2))
))
