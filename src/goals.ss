(library (goals)
  (export run-goal make-unification make-disj make-conj)
  (import (chezscheme) (substitution) (state) (streams))

  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))

  (define (run-goal g s)
    (cond
     [(unification? g)
      (let ([substitution (unify s (unification-lhs g) (unification-rhs g))])
	(if substitution (make-state substitution) #f))]
     [(disj? g) (mplus (run-goal (disj-lhs g) s) (run-goal (disj-rhs g) s))]
     ))

  )
