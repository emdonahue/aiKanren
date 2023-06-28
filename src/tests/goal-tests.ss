(library (goal-tests)
  (export run-goal-tests)
  (import (chezscheme) (test-runner) (aikanren))
  
  (define (run-goal-tests)

    (tassert "goal == simplifies atoms fail" (== 1 2) fail)

    ))
