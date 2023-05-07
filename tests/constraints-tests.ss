(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner))

  (define (run-constraints-tests)
    (tassert "disequality ground-ground" 1 1)
    
    ))
