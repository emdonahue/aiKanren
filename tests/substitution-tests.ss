(library (substitution-tests)
  (export run-substitution-tests)
  (import (chezscheme) (substitution) (test-runner) (failure))

  (define (run-substitution-tests)
    (define x0 (make-var 0))
    (define x1 (make-var 1))

    (tassert "substitution walk ground" (walk empty-substitution 1) 1)
    (tassert "substitution walk free" (walk empty-substitution x0) x0)
    (tassert "unify ground-ground" (unify empty-substitution 1 1) empty-substitution)
    (tassert "unify free-ground" (walk (unify empty-substitution x0 1) x0) 1)
    (tassert "unify free-ground" (walk (unify empty-substitution 1 x0) x0) 1)
    (tassert "unify variable to itself" (unify empty-substitution x0 x0) empty-substitution)
    (tassert "unify free-free" (walk (unify empty-substitution x0 x1) x0) x1)
    (tassert "unify free-free inverse priority" (walk (unify empty-substitution x1 x0) x0) x1)
    (tassert "unify cars" (walk (unify empty-substitution (cons x0 0) (cons 1 0)) x0) 1)
    (tassert "unify cars fail" (unify empty-substitution (cons 0 x0) (cons 1 0)) failure)
    (tassert "unify cdrs" (walk (unify empty-substitution (cons 0 x0) (cons 0 1)) x0) 1)
    (tassert "unify cdrs fail" (unify empty-substitution (cons x0 1) (cons 1 0)) failure)))



