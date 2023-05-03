(tassert "substitution walk ground" (walk substitution-empty 1) 1)
(tassert "substitution walk free" (walk substitution-empty (make-var 0)) (make-var 0))

(tassert "unify ground-ground" (unify substitution-empty 1 1) substitution-empty)
(tassert "unify free-ground" (walk (unify substitution-empty (make-var 0) 1) (make-var 0)) 1)



