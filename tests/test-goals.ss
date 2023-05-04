(tassert "unify goal ground-ground" (run-goal (make-unification 1 1) empty-state) empty-state)
(tassert "fresh unify free-ground" (walk (run-goal (fresh (x) (== x 1)) empty-state) (make-var 0)) 1)


