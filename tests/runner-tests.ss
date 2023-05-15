(library (runner-tests)
  (export run-runner-tests)
  (import (chezscheme) (ui) (test-runner) (datatypes))

  (define x1 (make-var 1))
  (define x2 (make-var 2))
  
  (define (run-runner-tests)
    (tassert "run unify free-ground" (run 1 (q) (== q 1)) '(1))
    (tassert "run unify free-ground take all" (run 2 (q) (== q 1)) '(1))
    (tassert "run conj no-ops" (run 1 (q) (== 2 2) (== q q) (== q 1) (== 2 2)) '(1))
    (tassert "run conj two bindings" (run 1 (q r) (== q 1) (== r 2)) '((1 2)))
    (tassert "run disj 2 empty states" (run* () (conde [(== 1 1)] [(== 2 2)])) '(() ()))
    (tassert "run disj 3 empty states" (run* () (conde [(== 1 1)] [(== 2 2)] [(== 3 3)])) '(() () ()))
    (tassert "run disj 3 unifications" (run* (q) (conde [(== q 1)] [(== q 2)] [(== q 3)])) '(1 2 3)) 
    (tassert "fresh" (run* (q) (fresh (x1) (== q x1) (== x1 1))) '(1))

    (tassert "succeed goal" (run* (x1) succeed) (list x1))
    (tassert "fail goal" (run* (x1) fail) '())
    (tassert "conj fail" (run* (x1) (fresh () succeed fail)) '())
    (tassert "conj fail 2" (run* (x1) (fresh () fail succeed)) '())
    (tassert "incomplete" (run* (x1) (fresh (x2) (fresh (x3) (fresh (x4) (== x1 42))))) '(42))
    
    (tassert "mplus fail lhs" (run* (x1) (conde [fail] [(== x1 1)])) '(1))
    (tassert "mplus fail rhs" (run* (x1) (conde [(== x1 1)] [fail])) '(1))
    (tassert "mplus answer lhs" (run* (x1) (conde [(== x1 1)] [(== x1 2)])) '(1 2))
    (tassert "mplus answer rhs" (run* (x1) (conde [(fresh (x2) (== x1 2))] [(== x1 1)])) '(1 2))
    (tassert "mplus complete lhs" (run* (x1) (conde [(conde [(== x1 1)] [(== x1 3)])] [(== x1 2)])) '(1 2 3))
    (tassert "mplus complete rhs" (run* (x1) (conde [(fresh (x2) (== x1 3))] [(conde [(== x1 1)] [(== x1 2)])])) '(1 2 3))
    (tassert "mplus incomplete" (run* (x1) (conde [(fresh (x2) (fresh (x3) (== x1 2)))] [(fresh (x2) (== x1 1))])) '(1 2))

    (tassert "bind incomplete" (run* (x1) (fresh (x2) (fresh (x3) (== x3 x2) (== x3 42)) (== x2 x1))) '(42))
    
    
    ))
