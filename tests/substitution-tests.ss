(library (substitution-tests)
  (export run-substitution-tests)
  (import (chezscheme) (substitution) (test-runner) (failure) (values) (constraints))

  (define (run-substitution-tests)
    (define x0 (make-var 0))
    (define x1 (make-var 1))

    (tassert "substitution walk ground" (walk empty-substitution 1) 1)
    (tassert "substitution walk free" (walk empty-substitution x0) x0)
    (tassert "unify ground-ground" (list-values (unify empty-substitution 1 1)) (list empty-substitution '()))
    (tassert "unify free-ground" (walk (first-value (unify empty-substitution x0 1)) x0) 1)
    (tassert "unify diseq free-ground" (values-ref (unify empty-substitution x0 1) 1) (list (cons x0 1)))
    (tassert "unify free-ground" (walk (first-value (unify empty-substitution 1 x0)) x0) 1)
    (tassert "unify variable to itself" (first-value (unify empty-substitution x0 x0)) empty-substitution)
    (tassert "unify free-free" (walk (first-value (unify empty-substitution x0 x1)) x0) x1)
    (tassert "unify free-free inverse priority" (walk (first-value (unify empty-substitution x1 x0)) x0) x1)
    (tassert "unify cars" (walk (first-value (unify empty-substitution (cons x0 0) (cons 1 0))) x0) 1)
    (tassert "unify cars fail" (first-value (unify empty-substitution (cons 0 x0) (cons 1 0))) failure)
    (tassert "unify cdrs" (walk (first-value (unify empty-substitution (cons 0 x0) (cons 0 1))) x0) 1)
    (tassert "unify cdrs fail" (first-value (unify empty-substitution (cons x0 1) (cons 1 0))) failure)
    (tassert "unify cars & cdrs car" (walk (first-value (unify empty-substitution (cons x0 1) (cons 0 x1))) x0) 0)
    (tassert "unify cars & cdrs cdr" (walk (first-value (unify empty-substitution (cons x0 1) (cons 0 x1))) x1) 1)
    (tassert "unify diseq cars & cdrs" (values-ref (unify empty-substitution (cons x0 1) (cons 0 x1)) 1)
	     (list (cons x0 0) (cons x1 1)))))



