;TODO delete datatypes.ss
(library (datatypes)
  (export make-var var? var-id var-equal?
	  succeed fail succeed? fail?
	  make-state empty-state state? set-state-substitution state-constraints state-substitution state-varid increment-varid instantiate-var set-state-constraints
	  failure failure? guarded? answer? state-or-failure?
	  make-constraint constraint? empty-constraint empty-constraint-store set-disequality constraint-store? constraint-goal constraint-store-constraints make-constraint-store constraint-disequality set-constraint-goal
	  satisfied satisfied? unsatisfiable unsatisfiable?
	  make-absento absento?
	  =/= =/=? =/=-lhs =/=-rhs disequality? empty-disequality disequality-null?
	  make-substitution empty-substitution substitution-dict substitution?
	  absento
	  make-== ==? ==-lhs ==-rhs disj make-disj disj* disj? disj-car disj-cdr disj-disjuncts goal? fresh? make-conj conj conj* conj? conj-car conj-cdr conj-conjuncts == make-stale stale? stale-fresh)
  (import (chezscheme) (sbral))

  ;; === VAR ===
  (define-structure (var id))
  (define var-equal? equal?)
  
  ;; === STREAMS ===
  (define failure '())
  (define failure? null?)
  
  ;; === GOALS ===
  
  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

    ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints))
  (define-structure (constraint disequality goal absento))
  (define-structure (absento atom term))
  (define empty-constraint (make-constraint '() succeed succeed))
  (define empty-constraint-store (make-constraint-store '()))
  (define (set-disequality c d)
    (assert (and (constraint? c) (disequality? d)))
    (let ([c (vector-copy c)])
      (set-constraint-disequality! c d) c))
  (define (set-constraint-goal c g)
    (assert (and (constraint? c) (goal? g)))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))
 (define satisfied (make-constraint 'satisfied '_ '_))
  (define (satisfied? c) (eq? c satisfied)) ;TODO rename constraint so that constraint? can include non-structure elements such as satisfied/unsatisfiable
  (define unsatisfiable (make-constraint 'unsatisfiable '_ '_))
  (define (unsatisfiable? c) (eq? c unsatisfiable))

    ;; === SUBSTITUTION ===
  (define-structure (substitution dict))
  (define empty-substitution (make-substitution sbral-empty))
  
  ;; === STATE ===
  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store '() #f 0))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))

  (define (increment-varid s)
    (assert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))

  (define (state-or-failure? s) (or (state? s) (failure? s)))

  (define (instantiate-var s)
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === STREAMS ===

  (define (answer? s)
    (and (state? s) (null? (state-guards s))))
  
  (define (guarded? s)
    (and (state? s) (not (null? (state-guards s)))))
    
  ;; === ABSENTO ===
  (define absento make-absento)

  ;; === DISEQUALITY ===
  (define-values (empty-disequality disequality? disequality-car disequality-cdr disequality-null?)
    (values '() list? car cdr null?))
  (define-structure (=/= lhs rhs))
  (define =/= make-=/=)

  ;; === GOALS ===
  (define-structure (== lhs rhs))
  (define-structure (conj conjuncts))
  (define-structure (disj disjuncts))
  (define-structure (stale fresh)) ; Negated fresh goal. Work with me here.

  (define == make-==)

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (=/=? g) (stale? g)))

  (define (conj conjuncts)
    (assert (list? conjuncts))
    ;;TODO move failures to the front so they run first, but do not fail immediately in case we need to negate
    ;;TODO append subconjuncts into a flat list
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
    (disj (cdr (disj-disjuncts d))))
)
