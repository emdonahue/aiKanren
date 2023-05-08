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
     )
    )
)
