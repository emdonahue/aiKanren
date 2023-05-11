(library (state)
  (export reify unify instantiate-var walk run-constraint)
  (import (chezscheme) (prefix (substitution) substitution:) (var) (failure) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (substitution:walk (state-substitution s) v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))
  
  (define (unify s x y)
    (assert (state? s))
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])      
      (check-constraints (set-state-substitution s sub) extensions)))

  (define (walk s v)
    (substitution:walk (state-substitution s) v))

  ;; === CONSTRAINTS === 
  
  (define (check-constraints s g)
    ;; Runs after unification to propagate new extensions through the constraint store. g is the goal representing the updates made to the substitution by the unifier.
    (assert (and (state-or-failure? s) (goal? g)))
    (cond
     [(or (failure? s) (fail? g)) failure] ; State has failed
     [(succeed? g) s] ; State has succeeded without modification     
     [(==? g) (run-constraint
	       (get-constraint (state-constraints s)
			       (==-lhs g)) s)] ; State has updated a single variable
     [(conj? g) (check-constraints (check-constraints s (conj-car g)) (conj-cdr g))]
     [else (assert #f)]))

  (define (run-constraint g s)
    (assert (and (state-or-failure? s) (goal? g)))
    (apply-constraints s (simplify-constraint g s)))

  (define (simplify-constraint g s)
    ;; Reduce the constraint to simplest form given the current substitution
    (assert (and (goal? g) (state? s)))
    (cond
     [(or (succeed? g)) (fail? g) g]
     [(=/=? g) (noto (values-ref (substitution:unify (state-substitution s) (=/=-lhs g) (=/=-rhs g)) 1))]
     [(conj? g) (normalized-conj (map (lambda (g) (simplify-constraint g s)) (conj-conjuncts g)))]
     [(disj? g) (normalized-disj (map (lambda (g) (simplify-constraint g s)) (disj-disjuncts g)))]))

    (define (get-attributed-vars c)
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (assert (not (conj? c))) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (if (disj? c)
	(get-attributed-vars (disj-car c)) ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
	(filter var? (vector->list c))))
  
  (define (apply-constraints s c)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state? s) (goal? c))) ; -> state?
    (cond
     [(succeed? c) s]
     [(fail? c) failure]
     [(conj? c) (fold-left apply-constraints s (disj-disjuncts c))] ; Conjoined constraints simply apply constraints independently.
     [else ; All other constraints get assigned to their attributed variables.
      (fold-left
       (lambda (s v)
	 (set-state-constraints
	  s (add-constraint (state-constraints s) v c))) s (get-attributed-vars c))])))
