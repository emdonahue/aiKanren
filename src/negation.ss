(library (negation)
  (export noto)
  (import (chezscheme) (datatypes))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(==? g) (make-noto g)]
     [(disj? g) (make-conj (map noto (disj-disjuncts g)))]
     [(conj? g) (make-disj (map noto (conj-conjuncts g)))]
     [(fresh? g) (make-noto g)]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (make-constraint (noto (constraint-goal g)))]
     [else (assert #f)]
     )
    )
)
