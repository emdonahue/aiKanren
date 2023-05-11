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
    (first-value (simplify-unification s x y)))

  (define (simplify-unification s x y)
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])      
      (values (check-constraints (set-state-substitution s sub) extensions) extensions)))

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

  #;
  (define (run-constraint g s)
    (assert (and (state-or-failure? s) (goal? g)))
    (apply-constraints s (simplify-constraint g s)))

  (define (run-constraint g s)
    ;; Simplify the constraint and push it into the store.
    (assert (and (goal? g) (state? s)))
    (cond
     [(succeed? g) s]
     [(fail? g) failure]
     [(==? g) (values-ref (simplify-constraint g s) 1)]
     [(=/=? g) (apply-constraints s (first-value (simplify-constraint g s)))]
     [(conj? g) (fold-left
		 (lambda (s g)
		   (let-values ([(g s) (simplify-constraint g s)])
		     (apply-constraints s g))) s (conj-conjuncts g))]
     [(disj? g) (apply-constraints s (normalized-disj (map (lambda (g) (first-value (simplify-constraint g s))) (disj-disjuncts g))))]
     [else (assert #f)]))

  (define (simplify-constraint g s)
    ;; Reduce the constraint to simplest form given the current substitution.
    (assert (and (goal? g) (state? s)))
    (cond
     [(succeed? g) (values g s)]
     [(fail? g) (values g failure)]
     [(==? g)
      (let-values ([(s g) (simplify-unification s (==-lhs g) (==-rhs g))])
	(values g s))]
     [(=/=? g) (values (noto (values-ref (substitution:unify (state-substitution s) (=/=-lhs g) (=/=-rhs g)) 1)) s)]
     [else (assert #f)])
    )

  (define (get-attributed-vars c)
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (assert (not (conj? c))) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (if (disj? c)
	(get-attributed-vars (disj-car c)) ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
	(filter var? (vector->list c))))
  
  (define (apply-constraints s c)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state-or-failure? s) (goal? c))) ; -> state?
    (cond
     [(or (failure? s) (fail? c)) failure]
     [(succeed? c) s]
     [(==? c) s] ; Bare unifications are stored in the substitution
     [(conj? c) (fold-left apply-constraints s (conj-conjuncts c))] ; Conjoined constraints simply apply constraints independently.
     [else ; All other constraints get assigned to their attributed variables.
      (fold-left
       (lambda (s v)
	 (set-state-constraints
	  s (add-constraint (state-constraints s) v c))) s (get-attributed-vars c))])))
