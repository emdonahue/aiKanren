(library (negation)
  (export noto =/=)
  (import (chezscheme) (datatypes))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(or (==? g) (pconstraint? g)) (make-noto g)]
     [(disj? g) (conj (noto (disj-car g)) (noto (disj-cdr g)))]
     [(conde? g) (conj (noto (conde-lhs g)) (noto (conde-rhs g)))]
     [(conj? g) (disj (noto (conj-car g)) (noto (conj-cdr g)))]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (noto (constraint-goal g))]
     [else (assertion-violation 'noto "Unrecognized constraint type" g)]))

  (define (=/= lhs rhs)
    (assert (not (or (goal? lhs) (goal? rhs))))
    (noto (== lhs rhs))))
