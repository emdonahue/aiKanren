(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (values))

  (define (run-matcho-tests)

    (tassert "match list fail" (run1 () (let ([m '(1 2)]) (matcho ([m (a 1)])))) (void))
    (tassert "match list succeed" (run1 () (let ([m '(1 1)]) (matcho ([m (a 1)])))) '())
    (tassert "match list extract" (run1 (x1 x2) (let ([m '(1 2)]) (matcho ([m (a b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match list extend" (run1 (x1) (let ([m (list 1 x1)]) (matcho ([m (a 2)])))) 2)
    (tassert "match pair fail" (run1 () (let ([m '(1 . 2)]) (matcho ([m (a . 1)])))) (void))
    (tassert "match pair succeed" (run1 () (let ([m '(1 . 1)]) (matcho ([m (a . 1)])))) '())
    (tassert "match pair extract" (run1 (x1 x2) (let ([m '(1 . 2)]) (matcho ([m (a . b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match pair extend" (run1 (x1) (let ([m (cons 1 x1)]) (matcho ([m (a . 2)])))) 2)
    (tassert "match pair symbol" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho ([m (a . 'two)]) (== a x1)))) '(one two))
    (tassert "match pair symbol list" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho ([m (a . '(two three))]) (== a x1)))) '(one (two three)))
    (tassert "match duplicate vars" (run1 (x1) (let ([m '(1 2)] [n (list x1 2)]) (matcho ([m (a 2)] [n (a 2)])))) 1)
    

    (tassert "match eager" (run* (x1) (conde [(let ([m (list 1 2)]) (matcho ([m (a 2)]) (== a x1)))] [(== x1 2)])) '(1 2))
    (tassert "match eager var" (run* (x1) (conde [(let ([m (list x1 2)]) (matcho ([m (a 2)]) (== a 1)))] [(== x1 2)])) '(1 2))
    (tassert "match eager bound var" (run* (x1) (conde [(== x1 '(1 2)) (matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2))
    (tassert "match lazy var" (run* (x1) (conde [(matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '(2 (1 2)))

    ;;TODO test matcho with unwalked vars

    (tassert "match ground constraint" (run* (x1) (let ([m '(1 2)]) (constrain (matcho ([m (a 2)]) (== a x1))))) '(1))
;    (tassert "match free constraint" (run* (x1) (let ([m (list x1 2)]) (constrain (matcho ([m (a 2)]) (== a 1))))) 1)

    ))
