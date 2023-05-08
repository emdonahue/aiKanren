(library (negation)
  (export noto)
  (import (chezscheme) (goals) (constraints))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(unification? g) (=/= (unification-lhs g) (unification-rhs g))]
     [(=/=? g) (== (=/=-lhs g) (=/=-rhs g))]
     [(disj? g) (make-conj (map noto (disj-disjuncts g)))]
     [(conj? g) (make-disj (map noto (conj-conjuncts g)))]
     [(fresh? g) (make-stale g)]
     [(stale? g) (stale-fresh g)]
     [else (assert #f)]
     )
    )
)
