(import (test-runner) (aikanren) (variables) (goals))

(define x1 (make-var 1))

(test-suite
 negation
 
 (tassert "negate succeed" (noto succeed) fail)
 (tassert "negate fail" (noto fail) succeed)
 (tassert "negate unification" (noto (== x1 2)) (make-noto (== x1 2)))
 (tassert "negate disunification" (noto (noto (== x1 2))) (== x1 2))
 (tassert "negate disjunction" (noto (conde [(=/= x1 2)] [succeed] [fail])) (conj* (== x1 2) fail succeed))
 (tassert "negate conjunction" (noto (conj* (== x1 2) fail succeed)) succeed))
