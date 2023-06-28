(library (listo-tests)
  (export run-listo-tests)
  (import (chezscheme) (test-runner) (aikanren))
  
  (define (run-listo-tests)

    (tassert "append empty" (run1 (x1) (appendo '() '() x1)) '())
    (tassert "append empty head" (run1 (x1) (appendo '(1) '() x1)) '(1))
    (tassert "append empty tail" (run1 (x1) (appendo '() '(1) x1)) '(1))
    (tassert "append empty tail" (run1 (x1) (appendo '() '(1) x1)) '(1))
    (tassert "append lists of 2" (run 4 (x1 x2) (appendo x1 x2 '(1 2))) '((() (1 2)) ((1) (2)) ((1 2) ())))
    ))
