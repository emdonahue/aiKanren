;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus unify-check)
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes) (prefix (substitution) substitution:)) 

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(succeed? g) (values succeed s p)]
     [(fail? g) (values fail failure p)]
     [(==? g) (let-values ([(s g) (unify-check s (==-lhs g) (==-rhs g))])
		(values g s p))]
     [(fresh? g) (let-values ([(g s p) (g s p)])
		   (values g (make-incomplete g s) p))]
     [(conj? g) (let*-values ([(g0 s p) (run-goal (conj-car g) s p)]
			     [(g s p) (bind (conj-cdr g) s p)])
		  (values (normalized-conj* g0 g) s p))]
     [(disj? g) (let*-values
		    ([(lhg lhs p) (run-goal (disj-car g) s p)]
		     [(rhg rhs p) (run-goal (disj-cdr g) s p)])
		  (values (normalized-disj* lhg rhg) (mplus lhs rhs) p))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) (g s p)])
					       (run-goal (noto g) s p))]
     [(and (noto? g) (not (fresh? (noto-goal g))))
      (let*-values ([(g s^ p) (run-goal (noto-goal g) s p)]
		    [(g) (noto g)])
	(values g (store-constraint s g) p))]
     [(constraint? g)
      (let*-values ([(g s^ p) (run-goal (constraint-goal g) s p)]
		   [(g s^ p) (run-constraint g s^ p)])
	(values g (store-constraint (copy-varid s^ s) g) p))]
     [else (assert #f)]))

  (define (run-constraint g s p)
    (assert (and (goal? g) (stream? s) (package? p)))
    (if (incomplete? s)
	(let-values ([(g s p) (stream-step s p)])
	  (run-constraint g s p))
	(values g s p)))
  
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
     [(failure? s) (values fail failure p)]
     [(state? s) (let-values ([(g^ s p) (run-goal g s p)])
		   (values (normalized-conj* g g^) s p))]
     [(or (incomplete? s) (mplus? s)) (values g (make-incomplete g s) p)]
     [(complete? s)
      (let*-values
	  ([(xxx h p) (run-goal g (complete-car s) p)]
	   [(xxx r p) (bind g (complete-cdr s) p)])
	(values 'bind-complete (mplus h r) p))]
     [else (assert #f)]))
  
  (define (stream-step s p)
    ;; TODO should stream-step return goals?
    (assert (and (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values fail s p)]
     [(state? s) (values succeed s p)]
     [(incomplete? s)
      (let*-values ([(g^ s^ p) (stream-step (incomplete-stream s) p)]
		    [(g s p) (bind (incomplete-goal s) s^ p)])
	(values (normalized-conj* g g^) s p))]
     [(mplus? s) (let-values ([(g lhs p) (stream-step (mplus-lhs s) p)])
		   (values 'step-goal (mplus (mplus-rhs s) lhs) p))]
     [(complete? s) (values 'step-goal (complete-cdr s) p)]
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
     [(conj? g) (check-constraints (check-constraints s (conj-car g)) (conj-cdr g))]
     [else (assert #f)]))

  (define (fire-constraint s e)
    (assert (and (state? s) (==? e)))
    (let-values ([(g s^ p) (run-goal
			    (get-constraint (state-constraints s)
					    (==-lhs e))
			    (set-state-constraints s (remove-constraint (state-constraints s) (==-lhs e)))
			    empty-package)])
      (store-constraint s g)))
  
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
