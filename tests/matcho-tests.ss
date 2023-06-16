(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (values))

  (define (run-matcho-tests)
    (tassert "match ground list fail" (run1 () (let ([p '(1 2)]) (matcho ([p (a b)]) (== a b)))) (void))
    (tassert "match ground list succeed" (run1 () (let ([p '(1 1)]) (matcho ([p (a b)]) (== a b)))) '())
    (tassert "match ground list extract" (run1 (x1 x2) (let ([p '(1 2)]) (matcho ([p (a b)]) (== x1 a) (== x2 b)))) '(1 2))
    (print-gensym #f)
 ;   (pretty-print (list-values (let ([p '(1 2)]) (expand '(matcho ([p (a b)]) (== a b))))))
;    (pretty-print (list-values ((let ([p '(1 2)]) (matcho ([p (a b)]) (== a b))) empty-state)))
    
    ))
