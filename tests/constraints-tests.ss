(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner) (state) (constraints))

  (define (run-constraints-tests)
    (disunify 3 1 1)
;    (tassert "disequality ground-ground" (disunify) 1)
    ))
