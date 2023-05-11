(library (negation)
  (export noto)
  (import (chezscheme) (datatypes))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(==? g) (=/= (==-lhs g) (==-rhs g))]
     [(=/=? g) (== (=/=-lhs g) (=/=-rhs g))]
     [(disj? g) (make-conj (map noto (disj-disjuncts g)))]
     [(conj? g) (make-disj (map noto (conj-conjuncts g)))]
     [(fresh? g) (make-noto g)]
     [(noto? g) (noto-goal g)]
     [else (assert #f)]
     )
    )
)
