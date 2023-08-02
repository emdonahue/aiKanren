(library (negation)
  (export noto =/= =/=-lhs =/=-rhs)
  (import (chezscheme) (datatypes) (utils))

  (define (noto g)
    (cert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(or (==? g) (matcho? g) (pconstraint? g)) (make-noto g)]
     [(disj? g) (conj (noto (disj-car g)) (noto (disj-cdr g)))]
     [(conde? g) (conj (noto (conde-lhs g)) (noto (conde-rhs g)))]
     [(conj? g) (disj (noto (conj-car g)) (noto (conj-cdr g)))]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (noto (constraint-goal g))]
     [else (assertion-violation 'noto "Unrecognized constraint type" g)]))
  
  (define (=/= lhs rhs)
    (cert (not (or (goal? lhs) (goal? rhs))))
    (noto (== lhs rhs)))
  (define (=/=-lhs g) (==-lhs (noto-goal g)))
  (define (=/=-rhs g) (==-rhs (noto-goal g))))
