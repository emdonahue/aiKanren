(library (runner-tests)
  (export run-runner-tests)
  (import (chezscheme) (ui) (test-runner))

  (define (run-runner-tests)
    (tassert "run unify free-ground" (run 1 (q) (== q 1)) '(1))
    (tassert "run unify free-ground take all" (run 2 (q) (== q 1)) '(1))))
