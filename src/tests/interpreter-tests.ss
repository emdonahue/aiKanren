(library (interpreter-tests)
  (export run-interpreter-tests)
  (import (chezscheme) (test-runner) (aikanren) (interpreter))
  
  (define (run-interpreter-tests)
    
    (tassert "evalo quote" (evalo '(quote 42)) 42)
    (tassert "evalo number" (evalo 42) 42)
    (tassert "evalo lookup val" (evalo 'x '((x . (val . 42)))) 42)
    (tassert "evalo shadow quote" (evalo '(quote 42) '((quote . (val . 43)))) (void))

    
))
