(library (substitution-tests)
  (export run-substitution-tests)
  (import (chezscheme) (substitution) (test-runner) (values) (datatypes))

  (define (run-substitution-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))

    (tassert "substitution walk ground" (walk empty-substitution 2) 2)
    (tassert "substitution walk free" (walk empty-substitution x1) x1)
    (tassert "unify ground-ground" (list-values (unify empty-substitution 2 2)) (list empty-substitution succeed))
    (tassert "unify free-ground" (walk (first-value (unify empty-substitution x1 2)) x1) 2)
    (tassert "unify diseq free-ground" (values-ref (unify empty-substitution x1 2) 1) (== x1 2))
    (tassert "unify free-ground" (walk (first-value (unify empty-substitution 2 x1)) x1) 2)
    (tassert "unify variable to itself" (first-value (unify empty-substitution x1 x1)) empty-substitution)
    (tassert "unify free-free" (walk (first-value (unify empty-substitution x1 x2)) x1) x2)
    (tassert "unify free-free inverse priority" (walk (first-value (unify empty-substitution x2 x1)) x1) x2)
    (tassert "unify cars" (walk (first-value (unify empty-substitution (cons x1 1) (cons 2 1))) x1) 2)
    (tassert "unify cars fail" (first-value (unify empty-substitution (cons 1 x1) (cons 2 1))) failure)
    (tassert "unify cdrs" (walk (first-value (unify empty-substitution (cons 1 x1) (cons 1 2))) x1) 2)
    (tassert "unify cdrs fail" (first-value (unify empty-substitution (cons x1 2) (cons 2 1))) failure)
    (tassert "unify cars & cdrs car" (walk (first-value (unify empty-substitution (cons x1 2) (cons 1 x2))) x1) 1)
    (tassert "unify cars & cdrs cdr" (walk (first-value (unify empty-substitution (cons x1 2) (cons 1 x2))) x2) 2)
    (tassert "unify diseq cars & cdrs" (values-ref (unify empty-substitution (cons x1 2) (cons 1 x2)) 1)
	     (conj* (== x1 1) (== x2 2)))))



