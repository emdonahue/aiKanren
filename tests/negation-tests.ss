(library (negation-tests)
  (export run-negation-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes))

  (define (run-negation-tests)
    (define x1 (make-var 1))
    
    (tassert "negate succeed" (noto succeed) fail)
    (tassert "negate fail" (noto fail) succeed)
    (tassert "negate unification" (noto (== 1 2)) (make-noto (== 1 2)))
    (tassert "negate disunification" (noto (noto (== 1 2))) (== 1 2))
    (tassert "negate disjunction" (noto (conde [(=/= 1 2)] [succeed] [fail])) (fresh () (== 1 2) fail succeed))
    (tassert "negate conjunction" (noto (fresh () (== 1 2) fail succeed)) succeed)
    (tassert "negate fresh" (noto? (noto (fresh (q) succeed))) #t)
    (tassert "negate noto" (fresh? (noto (noto (fresh (q) succeed)))) #t)

    ;(tassert "negate nested fresh" (run1 (x1) (noto (fresh (x2) (fresh (x3) (conde [(== x1 1)] [(== x1 2)]))))) (conj* (noto (== x1 2)) (noto (== x1 1))))
    ;(tassert "negate stream" (run* (x1) (noto (fresh (x2) (fresh (x3) (== x1 1)) (fresh (x3) (== x1 2))))) (list (noto (== x1 1)) (noto (== x1 2))))
    
    ))
