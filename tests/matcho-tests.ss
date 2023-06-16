(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (values))

  (define (run-matcho-tests)
					;(tassert "match ground pair" (let ([p '(1 . 2)]) (matcho ([p (a . b)]) (== a b))) 1)
    (print-gensym #f)
    (pretty-print (list-values (let ([p '(1 2)]) (expand '(matcho ([p (a b)]) (== a b))))))
    (pretty-print (list-values ((let ([p '(1 2)]) (matcho ([p (a b)]) (== a b))) empty-state)))
    
    ))
