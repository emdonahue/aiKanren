(library (goals)
  (export make-unification unification? unification-lhs unification-rhs make-conj conj-lhs conj-rhs make-disj disj-lhs disj-rhs goal? fresh? succeed fail succeed? fail? conj* conj?)
  (import (chezscheme))

  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))

  (define succeed 'succeed)
  (define fail 'fail)
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (unification? g) (conj? g) (disj? g)))

  (define (conj a b)
    (if (succeed? b) a (make-conj a b)))
  
  (define (conj* . conjs)
    (fold-right conj succeed conjs)))
