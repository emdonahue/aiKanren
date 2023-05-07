(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner) (state) (constraints) (failure))

  (define (run-constraints-tests)
    (tassert "disunify always equal" (disunify empty-state 1 1) failure)
    (tassert "disunify always disequal" (disunify empty-state 1 2) empty-state)
    ))
