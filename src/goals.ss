(library (goals)
  (export make-unification unification? unification-lhs unification-rhs make-conj make-disj disj-lhs disj-rhs goal? fresh? succeed fail succeed? fail? conj conj* conj? conj-car conj-cdr)
  (import (chezscheme))

  (define-structure (unification lhs rhs))
  (define-structure (conj conjuncts))
  (define-structure (disj lhs rhs))

  (define succeed 'succeed)
  (define fail 'fail)
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (unification? g) (conj? g) (disj? g) (succeed? g) (fail? g)))

  (define (conj conjuncts)
    (if (null? conjuncts) succeed (make-conj conjuncts)))
  
  (define (conj* . conjs)
    (conj conjs))

  (define (conj-car c)
    (assert (conj? c))
    (car (conj-conjuncts c)))

  (define (conj-cdr c)
    (assert (conj? c))
    (conj (cdr (conj-conjuncts c)))))
