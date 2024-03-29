(library (matcho-tests)
  (export run-matcho-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (utils))

  (define (run-matcho-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))

    ;; Basic pattern matching
    (tassert "match list fail" (run1 () (let ([m '(1 2)]) (matcho ([m (a 1)])))) (void))
    (tassert "match list succeed" (run1 () (let ([m '(1 1)]) (matcho ([m (a 1)])))) '())
    (tassert "match list extract" (run1 (x1 x2) (let ([m '(1 2)]) (matcho ([m (a b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match list extend" (run1 x1 (let ([m (list 1 x1)]) (matcho ([m (a 2)])))) 2)
    (tassert "match pair fail" (run1 () (let ([m '(1 . 2)]) (matcho ([m (a . 1)])))) (void))
    (tassert "match pair succeed" (run1 () (let ([m '(1 . 1)]) (matcho ([m (a . 1)])))) '())
    (tassert "match pair extract" (run1 (x1 x2) (let ([m '(1 . 2)]) (matcho ([m (a . b)]) (== x1 a) (== x2 b)))) '(1 2))
    (tassert "match pair extend" (run1 x1 (let ([m (cons 1 x1)]) (matcho ([m (a . 2)])))) 2)
    (tassert "match pair symbol" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho ([m (a . 'two)]) (== a x1)))) '(one two))
    (tassert "match pair symbol list" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho ([m (a . '(two three))]) (== a x1)))) '(one (two three)))
    (tassert "match duplicate vars" (run1 x1 (let ([m '(1 2)] [n (list x1 2)]) (matcho ([m (a 2)] [n (a 2)])))) 1)
    (tassert "match optimized pair unifies cons" (run1 x1 (matcho ([x1 (a . d)]) (== a 1) (== d 2))) '(1 . 2))

    ;; Eagerly run matcho until we exhaust ground information
    #;
    (begin ;TODO revisit matcho eagerness if all ground
      (tassert "match eager" (run* (x1) (conde [(let ([m (list 1 2)]) (matcho ([m (a 2)]) (== a x1)))] [(== x1 2)])) '(1 2))
      (tassert "match eager var" (run* (x1) (conde [(let ([m (list x1 2)]) (matcho ([m (a 2)]) (== a 1)))] [(== x1 2)])) '(1 2))
      (tassert "match eager bound var" (run* (x1) (conde [(== x1 '(1 2)) (matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2))
      (tassert "match eager bound vars" (run* (x1 x2) (conde [(== x2 '(1 2)) (matcho ([x1 (a 2)] [x2 (1 2)]) (== a 1))] [(== x1 3) (== x2 4)])) '(((1 2) (1 2)) (3 4)))
      (tassert "match lazy var" (run* (x1) (conde [(matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '(2 (1 2))))

    ;; Constraint matcho
    (tassert "match constraint ground" (run1 x1 (let ([m '(1 2)]) (constraint (matcho ([m (a 2)]) (== a x1))))) 1)
    (tassert "match constraint ground-free" (run1 x1 (let ([m (list x1 2)]) (constraint (matcho ([m (a 2)]) (== a 1))))) 1)
    (tassert "match constraint free" (matcho-out-vars (run1 x1 (constraint (matcho ([x1 (a 2)]) (== a 1))))) (list x1))
    (tassert "match constraint disj first" (run1 (x1 x2) (constraint (matcho ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2))) (lambda (g) (and (equal? '(1 2) (car g)) (matcho-test-eq? (cadr g) (list x2) '((1 2))))))
    (tassert "match constraint disj rest" (matcho-out-vars (car (run1 (x1 x2) (constraint (matcho ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x2 '(1 2))))) (list x1 x2))
    (tassert "match constraint disj all" (run1 (x1 x2) (constraint (matcho ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2)) (== x2 x1)) '((1 2) (1 2)))
    (tassert "match constraint no fresh" (run1 (x1 x2) (constraint (matcho ([x1 (a b)]))) (== x1 (list x2 x2))) (list (list x2 x2) x2))
    (tassert "match constraint simplifies ground" (run1 (x1 x2) (constraint (matcho ([x1 (a . d)] [x2 (b . c)]) (== (list a d b c) '(1 2 3 4)))) (== x1 '(1 . 2)) (== x2 '(3 . 4))) '((1 . 2) (3 . 4)))
    (tassert "match constraint simplifies var" (run1 (x1 x2) (constraint (matcho ([x1 (a . d)] [x2 (b . c)]) (== a 1))) (== x1 x2) (== x2 '(1 . 2))) '((1 . 2) (1 . 2)))
    (tassert "match constraint rechecks var" (run1 (x1 x2 x3) (== x3 x2) (constraint (matcho ([x1 (a . d)] [x3 (b . c)]) (== a 1))) (== x1 '(1 . 2))) (lambda (g) (and (equal? (car g) '(1 . 2)) (matcho-test-eq? (cadr g) (list x3) '((1 . 2))) (matcho-test-eq? (caddr g) (list x3) '((1 . 2))))))

    ;; Negated matcho
    (tassert "match noto pattern fail" (run1 x1 (== x1 `(1 . 2)) (noto (matcho ([x1 (2 . y)]) succeed))) '(1 . 2))
    (tassert "match noto pattern succeed" (run1 x1 (== x1 `(1 . 2)) (noto (matcho ([x1 (1 . y)]) succeed))) (void))
    (tassert "match noto pattern disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho ([x1 (1 . y)]) succeed))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto contents disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho ([x1 (y . 2)]) (== 1 y)))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto optimized pair disequality" (run1 (x1 x2 x3) (== x1 `(,x2 . ,x3)) (noto (matcho ([x1 (y . z)]) (conde [(== y 1)] [(== z 2)])))) (list (cons (=/= x2 1) (=/= x3 2)) (=/= x2 1) (=/= x3 2)))))
