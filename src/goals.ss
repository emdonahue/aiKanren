(library (goals)
  (export make-== ==? ==-lhs ==-rhs disj make-disj disj* disj? disj-car disj-cdr disj-disjuncts goal? fresh? succeed fail succeed? fail? make-conj conj conj* conj? conj-car conj-cdr conj-conjuncts == make-stale stale? stale-fresh)
  (import (chezscheme) (constraints))

  (define-structure (== lhs rhs))
  (define-structure (conj conjuncts))
  (define-structure (disj disjuncts))
  (define-structure (stale fresh)) ; Negated fresh goal. Work with me here.

  ;;TODO convert succeed, fail, and failure to lists with symbols
  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))
  (define == make-==)

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (=/=? g) (stale? g)))

  (define (conj conjuncts)
    (assert (list? conjuncts))
    ;;TODO move failures to the front so they run first, but do not fail immediately in case we need to negate
    (cond
     [(null? conjuncts) succeed]
     [(null? (cdr conjuncts)) (car conjuncts)]
     [else (make-conj conjuncts)]))
  
  (define (conj* . conjs)
    (conj conjs))

  (define (conj-car c)
    (assert (conj? c))
    (car (conj-conjuncts c)))

  (define (conj-cdr c)
    (assert (conj? c))
    (conj (cdr (conj-conjuncts c))))

  (define (disj disjuncts)
    (assert (list? disjuncts))
    ;;TODO move successes to front of disj so they turn into failures if negated
    (cond
     [(null? disjuncts) fail]
     [(null? (cdr disjuncts)) (car disjuncts)]
     [else (make-disj disjuncts)]))

  (define (disj* . disjuncts)
    (disj disjuncts))

  (define (disj-car d)
    (car (disj-disjuncts d)))

  (define (disj-cdr d)
    (disj (cdr (disj-disjuncts d)))))
