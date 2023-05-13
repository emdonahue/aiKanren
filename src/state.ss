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

  (define (simplify-unification s x y) ;TODO remove simplify unification bc extensions will be wrong, but remember to unpack states
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
     [(==? g) (run-constraint ; TODO should we run a conjunction of all updated states at the same time, or would that just do the same thing?
	       (set-state-constraints s (remove-constraint (state-constraints s) (==-lhs g)))
	       (get-constraint (state-constraints s)
			       (==-lhs g)))] ; State has updated a single variable
     [(conj? g) (check-constraints (check-constraints s (conj-car g)) (conj-cdr g))]
     [else (assert #f)]))

  (define (run-constraint s g)
    ;; Simplify the constraint and push it into the store.
    (assert (and (state? s) (goal? g))) ; -> state-or-failure?
    (let-values ([(_ g) (run-simple-constraint s g)])
      (store-constraints s g)))
  
  (define (run-conj s gs c) ; g is input conjunct, c is simplified "output" conjunct
    ;; TODO reuse substitution when storing conjoined == constraints
    (assert (and (state-or-failure? s) (list? gs) (goal? c))) ; -> state-or-fail?
    (cond
     [(fail? c) (values failure fail)]
     [(null? gs) (values s c)]
     [else (let-values ([(s g) (run-simple-constraint s (car gs))])
	     (run-conj s (cdr gs) (if (and #f (==? (car gs)) (not (fail? g))) ; == already in substitution. No need to add to store.
				      c (normalized-conj (list g c)))))]))

    (define (run-disj s gs c ==-s)
      ;; s^ preserves the last state resulting from == in case we end up with only a single == and want to commit to it without re-unifying
      ;; TODO reuse substitution when disj constraint simplifies to ==
    (assert (and (state? s) (list? gs) (goal? c) (state-or-failure? ==-s))) ; -> state-or-failure?
    (cond
     [(succeed? c) (values s succeed)]
     [(null? gs) (values (if (==? c) ==-s s) c)] ; If committing to a single ==, reuse the substitution.
     [else (let-values ([(s^ g) (run-simple-constraint s (car gs))])
	     (run-disj s (cdr gs) (normalized-disj (list c g))
		       (if (and #f (==? (car gs)) (not (fail? g))) s^ ==-s)))]))

  (define (run-simple-constraint s g)
    (assert (and (state-or-failure? s) (goal? g))) ; -> state? goal?
    (cond
     [(or (failure? s) (fail? g)) (values failure g)]
     [(succeed? g) (values s g)]
     [(==? g) (simplify-unification s (==-lhs g) (==-rhs g))]
     [(=/=? g) (values s (noto (values-ref (simplify-unification s (=/=-lhs g) (=/=-rhs g)) 1)))]
     [(fresh? g) (run-simple-constraint s (first-value (g s empty-package)))]
     [(conj? g) (run-conj s (conj-conjuncts g) succeed)]
     [(disj? g) (run-disj s (disj-disjuncts g) fail failure)]
     [else (assert #f)]))  

  (define (get-attributed-vars c)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; TODO attributed vars should probably be deduplicated    
    (assert (not (conj? c))) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (if (disj? c)
	(get-attributed-vars (disj-car c)) ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
	(filter var? (vector->list c))))
  
  (define (store-constraints s c)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state-or-failure? s) (goal? c))) ; -> state?
    (cond
     [(or (failure? s) (fail? c)) failure]
     [(succeed? c) s]
     [(==? c) (unify s (==-lhs c) (==-rhs c))] ; Bare unifications are stored in the substitution
     [(conj? c) (fold-left store-constraints s (conj-conjuncts c))] ; Conjoined constraints simply apply constraints independently.
     [else ; All other constraints get assigned to their attributed variables.
      (fold-left
       (lambda (s v)
	 (set-state-constraints
	  s (add-constraint (state-constraints s) v c))) s (get-attributed-vars c))])))
