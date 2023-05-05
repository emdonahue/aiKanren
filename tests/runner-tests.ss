(library (runner-tests)
  (export run-runner-tests)
  (import (chezscheme) (ui) (test-runner))

  (define (run-runner-tests)
    (tassert "run unify free-ground" (run 1 (q) (== q 1)) '(1))
    (tassert "run unify free-ground take all" (run 2 (q) (== q 1)) '(1))
    (tassert "run conj no-ops" (run 1 (q) (== 2 2) (== q q) (== q 1) (== 2 2)) '(1))

    (display (runner-take 1 (runner (q) (== 2 2) (== q q) (== q 1) (== 2 2))))

    ))
