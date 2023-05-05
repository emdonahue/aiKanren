(library (goals)
  (export make-unification unification? unification-lhs unification-rhs make-conj conj-lhs conj-rhs make-disj disj-lhs disj-rhs goal? fresh?)
  (import (chezscheme))

  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (unification? g) (conj? g) (disj? g))))
