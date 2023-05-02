(tassert "substitution walk ground" (walk 1 substitution-empty) 1)

(tassert "unify ground" (unify 1 1 substitution-empty) substitution-empty)
