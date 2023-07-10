(library (interpreter-tests)
  (export run-interpreter-tests)
  (import (chezscheme) (test-runner) (aikanren) (interpreter))
  
  (define (run-interpreter-tests)
    
    (tassert "eval quote" (evalo '(quote 42)) 42)
    (tassert "eval number" (evalo 42) 42)
    (tassert "eval lookup val" (run1 (o) (evalo 'x '((x . (val . 42))) o)) 42)

    
))
