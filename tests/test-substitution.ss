(let ([x0 (make-var 0)] [x1 (make-var 1)])
  (tassert "substitution walk ground" (walk substitution-empty 1) 1)
  (tassert "substitution walk free" (walk substitution-empty x0) x0)
  (tassert "unify ground-ground" (unify substitution-empty 1 1) substitution-empty)
  (tassert "unify free-ground" (walk (unify substitution-empty x0 1) x0) 1)
  (tassert "unify free-ground" (walk (unify substitution-empty 1 x0) x0) 1)
  (tassert "unify variable to itself" (unify substitution-empty x0 x0) substitution-empty)
  (tassert "unify free-free" (walk (unify substitution-empty x0 x1) x0) x1)
  (tassert "unify free-free inverse priority" (walk (unify substitution-empty x1 x0) x0) x1)
  (tassert "unify cars" (walk (unify substitution-empty (cons x0 0) (cons 1 0)) x0) 1)
  (tassert "unify cars fail" (unify substitution-empty (cons 0 x0) (cons 1 0)) #f)
  (tassert "unify cdrs" (walk (unify substitution-empty (cons 0 x0) (cons 0 1)) x0) 1)
  (tassert "unify cdrs fail" (unify substitution-empty (cons x0 1) (cons 1 0)) #f)
  )



