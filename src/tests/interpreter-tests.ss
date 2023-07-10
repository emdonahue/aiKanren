(library (interpreter-tests)
  (export run-interpreter-tests)
  (import (chezscheme) (test-runner) (aikanren) (interpreter))
  
  (define (run-interpreter-tests)
    
    (tassert "evalo quote" (evalo '(quote 42)) 42)
    (tassert "evalo shadow quote" (evalo '(quote 42) '((quote . (val . 43)))) (void))
;    (tassert "evalo true" (evalo #t) #t)
;    (tassert "evalo false" (evalo #f) #f)
;    (tassert "evalo number" (evalo 42) 42)

    (tassert "evalo lookup val" (evalo 'x '((x . (val . 42)))) 42)
    
    (tassert "evalo lambda single arg" (evalo '(lambda x x) '((x . (val . 42)))) `(closure (lambda x x) ((x . (val . 42)) . ,initial-env)))
    (tassert "evalo lambda multi arg" (evalo '(lambda (x) x) '((x . (val . 42)))) `(closure (lambda (x) x) ((x . (val . 42)) . ,initial-env)))

;    (tassert "evalo and" (evalo '(and)) #t)
    
    (tassert "evalo apply" (evalo '(x 42) `((x . (val . ,(evalo '(lambda (x) x)))))) 42)

    (tassert "evalo apply variadic" (evalo '(x 42) `((x . (val . ,(evalo '(lambda x x)))))) '(42))

    (tassert "evalo list" (evalo '(list 42 42)) '(42 42))

;    (display (run 1 (q) (evalo q '() q)))
))
