(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren))

  (define (run-matcho-tests)
					;(tassert "match ground pair" (let ([p '(1 . 2)]) (matcho ([p (a . b)]) (== a b))) 1)
    (print-gensym #f)
    (display (let ([p '(1 . 2)]) (expand '(matcho ([p (a b a)]) (== a b)))))
;    (display (matcho ([p ('a . b)]) (== 'a b)))
    
    ))
