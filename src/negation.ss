(library (negation)
  (export noto)
  (import (chezscheme) (datatypes))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(or (==? g) (pconstraint? g)) (make-noto g)]
     [(disj? g) (conj (noto (disj-car g)) (noto (disj-cdr g)))]
     [(conj? g) (disj (noto (conj-car g)) (noto (conj-cdr g)))]
     [(fresh? g) (make-noto g)]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (make-constraint (noto (constraint-goal g)))]
     [else (assert #f)]
     )
    )
)
