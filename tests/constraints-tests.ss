(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner) (state) (constraints) (failure))

  (define (run-constraints-tests)
    (tassert "disunify ground-ground" (disunify empty-state 1 1) failure)
    
    ))
