(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (values))

  (define (run-matcho-tests)
    (print-gensym #f)
    ;(pretty-print (list-values (let ([p '(1 2)]) (expand '(matcho ([p (a 1)]) (== a 1))))))
    (tassert "match list fail" (run1 () (let ([p '(1 2)]) (matcho ([p (a 1)])))) (void))
    (tassert "match list succeed" (run1 () (let ([p '(1 1)]) (matcho ([p (a 1)])))) '())
    (tassert "match list extract" (run1 (x1 x2) (let ([p '(1 2)]) (matcho ([p (a b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match list extend" (run1 (x1) (let ([p (list 1 x1)]) (matcho ([p (a 2)])))) 2)
    (tassert "match pair fail" (run1 () (let ([p '(1 . 2)]) (matcho ([p (a . 1)])))) (void))
    (tassert "match pair succeed" (run1 () (let ([p '(1 . 1)]) (matcho ([p (a . 1)])))) '())
    (tassert "match pair extract" (run1 (x1 x2) (let ([p '(1 . 2)]) (matcho ([p (a . b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match pair extend" (run1 (x1) (let ([p (cons 1 x1)]) (matcho ([p (a . 2)])))) 2)
    ;(tassert "match pair symbols" (run1 (x1 x2) (let ([p (cons 'one x2)]) (matcho ([p (a . 'two)]) (== a x1)))) '(one two))
    ;TODO make matcho handle symbol extraction
    
    ))
