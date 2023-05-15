;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus unify-check)
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes) (prefix (substitution) substitution:)) 

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(succeed? g) (values succeed s p (state-varid s))]
     [(fail? g) (values fail failure p 0)]
     [(==? g) (let-values ([(s g) (unify-check s (==-lhs g) (==-rhs g))])
		(values g s p (if (failure? s) 0 (state-varid s))))]
     [(fresh? g) (let-values ([(g s p) (g s p)])
		   (values g (make-incomplete g s) p (state-varid s)))]
     [(conj? g) (let*-values ([(g0 s p lhv) (run-goal (conj-car g) s p)]
			     [(g s p rhv) (bind (conj-cdr g) s p)])
		  (values (normalized-conj* g0 g) s p (max lhv rhv)))]
     [(disj? g) (let*-values
		    ([(lhg lhs p lhv) (run-goal (disj-car g) s p)]
		     [(rhg rhs p rhv) (run-goal (disj-cdr g) s p)])
		  (values (normalized-disj* lhg rhg) (mplus lhs rhs) p (max lhv rhv)))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) (g s p)])
					       (run-goal (noto g) s p))]
     [(and (noto? g) (not (fresh? (noto-goal g))))
      (let*-values ([(g s^ p vid) (run-goal (noto-goal g) s p)]
		    [(g) (noto g)])
	(values g (store-constraint s g) p vid))]
     [(constraint? g)
      (let*-values ([(g s^ p vid) (run-goal (constraint-goal g) s p)]
		   [(g s^ p vid) (run-constraint g s^ p vid)])
	(values g (store-constraint (copy-max-varid s vid) g) p vid))]
     [else (assert #f)]))

  (define (run-constraint g s p v-start)
    (assert (and (goal? g) (stream? s) (package? p)))
    (if (incomplete? s)
	(let-values ([(g s p vid) (stream-step s p)])
	  (run-constraint g s p (max v-start vid)))
	(values g s p (max v-start v-start))))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (complete lhs rhs)]
     [(complete? lhs) (complete (complete-car lhs) (mplus rhs (complete-cdr lhs)))]
     [(answer? rhs) (complete rhs lhs)]
     [(complete? rhs) (complete (complete-car rhs) (mplus lhs (complete-cdr rhs)))]
     [else (make-mplus lhs rhs)]))

  (define (bind g s p)
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values fail failure p 0)]
     [(state? s) (let-values ([(g^ s p vid) (run-goal g s p)])
		   (values (normalized-conj* g g^) s p vid))]
     [(or (incomplete? s) (mplus? s)) (values g (make-incomplete g s) p 0)]
     [(complete? s) (let*-values
			([(lhg h p lhv) (run-goal g (complete-car s) p)]
			 [(rhg r p rhv) (bind g (complete-cdr s) p)])
		      (values (normalized-disj* lhg rhg) (mplus h r) p (max lhv rhv)))]
     [else (assert #f)]))
  
  (define (stream-step s p)
    ;; TODO should stream-step return goals?
    (assert (and (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values fail s p 0)]
     [(state? s) (values succeed s p (state-varid s))]
     [(incomplete? s)
      (let*-values ([(g^ s^ p lhv) (stream-step (incomplete-stream s) p)]
		    [(g s p rhv) (bind (incomplete-goal s) s^ p)])
	(values (normalized-conj* g g^) s p (max lhv rhv)))]
     [(mplus? s) (let-values ([(g lhs p vid) (stream-step (mplus-lhs s) p)])
		   (values 'step-goal (mplus (mplus-rhs s) lhs) p vid))]
     [(complete? s) (values 'step-goal (complete-cdr s) p (state-varid (complete-car s)))]
     [else (assert #f)]))


  ;; === CONSTRAINTS ===

  (define (unify-check s x y) ;TODO remove simplify unification bc extensions will be wrong, but remember to unpack states
    (assert (state? s)) ; -> state-or-failure? goal?
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])      
      (values (check-constraints (set-state-substitution s sub) extensions) extensions)))
  
  (define (check-constraints s g)
    ;; Runs after unification to propagate new extensions through the constraint store. g is the goal representing the updates made to the substitution by the unifier.
    (assert (and (state-or-failure? s) (goal? g)))
    (cond
     [(or (failure? s) (fail? g)) failure] ; State has failed
     [(succeed? g) s] ; State has succeeded without modification     
     [(==? g) (fire-constraint s g)] ; State has updated a single variable
     [(conj? g) (check-constraints (check-constraints s (conj-car g)) (conj-cdr g))] ; Updated multiple variables
     [else (assert #f)]))

  (define (fire-constraint s e)
    (assert (and (state? s) (==? e)))
    (let-values ([(g s^ p vid) (run-goal
			    (get-constraint (state-constraints s)
					    (==-lhs e))
			    (set-state-constraints s (remove-constraint (state-constraints s) (==-lhs e)))
			    empty-package)])
      (store-constraint (copy-max-varid s vid) g)))
  
  (define (store-constraint s c)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state-or-failure? s) (goal? c))) ; -> state?
    (cond
     [(or (failure? s) (fail? c)) failure]
     [(succeed? c) s]
     [(==? c) (first-value (unify-check s (==-lhs c) (==-rhs c)))] ; Bare unifications are stored in the substitution
     [(conj? c) (fold-left store-constraint s (conj-conjuncts c))] ; Conjoined constraints simply apply constraints independently.
     [else ; All other constraints get assigned to their attributed variables.
      (fold-left
       (lambda (s v)
	 (set-state-constraints
	  s (add-constraint (state-constraints s) v c))) s (get-attributed-vars c))]))

  (define (get-attributed-vars c)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; TODO attributed vars should probably be deduplicated    
    (assert (not (conj? c))) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (cond
     [(disj? c) (get-attributed-vars (disj-car c))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
     [(noto? c) (get-attributed-vars (noto-goal c))]
     [else (filter var? (vector->list c))]))) 
