(library (negation)
  (export noto =/= =/=-lhs =/=-rhs)
  (import (chezscheme) (datatypes) (utils))

  (define (noto g) ; Logical negation of constraints.
    ;; Goals wrapped with noto will be interpreted as negated constraints. Negation in this context should be understood in terms of a few simple operations:
    ;; == and =/= become the other when negated
    ;; conj and disj become the other when negated and their children are negated in accordance with De Morgan's laws
    ;; primitive constraints (such as symbolo) become negated versions of themselves (e.g. not-symbolo)
    ;; matcho lazily waits until it can expand and then negates its expansion
    ;; fresh cannot currently be negated
    
    (cert (goal? g))
    (exclusive-cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(or (==? g) (matcho? g) (pconstraint? g)) (make-noto g)]
     [(disj? g) (conj (noto (disj-car g)) (noto (disj-cdr g)))]
     [(conde? g) (conj (noto (conde-lhs g)) (noto (conde-rhs g)))]
     [(conj? g) (disj (noto (conj-car g)) (noto (conj-cdr g)))]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (noto (constraint-goal g))]
     [else (assertion-violation 'noto "Unrecognized constraint type" g)]))
  
  (define (=/= lhs rhs) ; Disequality between terms.
    (cert (not (or (goal? lhs) (goal? rhs))))
    (noto (== lhs rhs)))
  (define (=/=-lhs g) (==-lhs (noto-goal g)))
  (define (=/=-rhs g) (==-rhs (noto-goal g))))
