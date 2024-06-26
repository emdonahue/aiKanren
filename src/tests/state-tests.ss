(import (test-runner) (mk core state) (mk core utils) (mk core) (mk core reifier) (mk core walk))

(define x1 (var 1))
(define x2 (var 2))

(test-suite
 state

 (tassert "state walk ground" (walk empty-state 2) 2)
 (tassert "state walk free" (walk empty-state x1) x1)
 (tassert "state reify ground" (reify empty-state 2) 2)
 (tassert "state reify free" (reify empty-state x1) x1)
 (tassert "state reify bound" (reify (values-ref (unify empty-state succeed x1 1) 5) x1) 1)
 (tassert "state reify pair" (reify (values-ref (unify empty-state succeed x1 1) 5) (cons 2 (cons x1 x2))) (cons 2 (cons 1 x2)))
 (tassert "state unify ground-ground" (values-ref (unify empty-state succeed 2 2) 5) empty-state)
 (tassert "state unify free-ground" (walk (values-ref (unify empty-state succeed x1 2) 5) x1) 2)
 (tassert "state unify free-ground" (walk (values-ref (unify empty-state succeed 2 x1) 5) x1) 2)
 (tassert "state unify variable to itself" (values-ref (unify empty-state succeed x1 x1) 5) empty-state)
 (tassert "state unify free-free" (walk (values-ref (unify empty-state succeed x1 x2) 5) x1) x2)
 (tassert "state unify free-free inverse priority" (walk (values-ref (unify empty-state succeed x2 x1) 5) x1) x2)
 (tassert "state unify cars" (walk (values-ref (unify empty-state succeed (cons x1 1) (cons 2 1)) 5) x1) 2)
 (tassert "state unify cars fail" (values-ref (unify empty-state succeed (cons 1 x1) (cons 2 1)) 5) failure)
 (tassert "state unify cdrs" (walk (values-ref (unify empty-state succeed (cons 1 x1) (cons 1 2)) 5) x1) 2)
 (tassert "state unify cdrs fail" (values-ref (unify empty-state succeed (cons x1 2) (cons 2 1)) 5) failure))
