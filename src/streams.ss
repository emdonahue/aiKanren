;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus unify-check simplify-constraint check-constraints run-dfs) ; TODO trim exports
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes) (prefix (substitution) substitution:)) 

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(succeed? g) (values s p)]
     [(fail? g) (values failure p)]
     [(==? g) (let-values ([(s g) (unify-check s (==-lhs g) (==-rhs g))])
		(values s p))]
     [(fresh? g) (let-values ([(g s p) (g s p)]) ; TODO do freshes that dont change the state preserve low varid count?
		   (values (make-bind g s) p))]
     [(conj? g) (let*-values ([(s p) (run-goal (conj-car g) s p)]
			      [(s p) (bind (conj-cdr g) s p)])
		  (values s p))]
     [(disj? g) (let*-values
		    ([(lhs p) (run-goal (disj-car g) s p)]
		     [(rhs p) (run-goal (disj-cdr g) s p)])
		  (values (mplus lhs rhs) p))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) ((noto-goal g) s p)])
					       (values (make-bind (noto g) s) p))] 
     [(and (noto? g) (not (fresh? (noto-goal g)))) (values (run-constraint g s) p)]
     [(constraint? g) (values (run-constraint (constraint-goal g) s) p)]
     [(pconstraint? g) (values (run-constraint g s) p)]
     [else (assertion-violation 'run-goal "Unrecognized goal type" g)]))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (answers lhs rhs)]
     [(answers? lhs) (answers (answers-car lhs) (mplus rhs (answers-cdr lhs)))]
     [(answer? rhs) (answers rhs lhs)]
     [(answers? rhs) (answers (answers-car rhs) (mplus lhs (answers-cdr rhs)))]
     [else (make-mplus lhs rhs)]))

  (define (bind g s p)
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values failure p)]
     [(state? s) (let-values ([(s p) (run-goal g s p)])
		   (values s p))]
     [(or (bind? s) (mplus? s)) (values (make-bind g s) p)]
     [(answers? s) (let*-values
			([(h p lhv) (run-goal g (answers-car s) p)]
			 [(r p rhv) (bind g (answers-cdr s) p)])
		      (values (mplus h r) p))]
     [else (assert #f)]))
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values s p)]
     [(bind? s)
      (let*-values ([(s^ p) (stream-step (bind-stream s) p)]
		    [(s p) (bind (bind-goal s) s^ p)])
	(values s p))]
     [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) lhs) p))]
     [(answers? s) (values (answers-cdr s) p)]
     [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))

  (define (unify-check s x y) ;TODO remove simplify unification bc extensions will be wrong, but remember to unpack states
    (assert (state? s)) ; -> state-or-failure? goal?
    (let*-values ([(sub extensions) (substitution:unify (state-substitution s) x y)]
		 [(s) (check-constraints (set-state-substitution s sub) extensions)])      
      (if (failure? s) (values failure fail) (values s extensions))))

  (define (unify-no-check s x y)
    ;; to walk a term we need to keep at least the unifications in the state. maybe apply only unifications and ignore other constraints?
    (assert (state? s)) ; -> state-or-failure? goal?
    (let*-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])      
      (if (failure? s) (values failure fail) (values (set-state-substitution s sub) extensions))))

  ;; === CONSTRAINTS ===

  (define (run-constraint g s)
    (assert (and (goal? g) (state? s))) ; -> state-or-failure?
    (let-values ([(g s^ v) (simplify-constraint g (clear-state-constraints s))]) 
      (if (failure? s^) failure (store-constraint (set-state-varid s v) g))))

  (define (simplify-constraint g s)
    (assert (and (goal? g) (state-or-failure? s)))
    (cond
     [(failure? s) (values fail failure 0)]
     [(succeed? g) (values succeed s (state-varid s))]
     [(fail? g) (values fail failure 0)]
     [(==? g) (let-values ([(s g) (unify-no-check s (==-lhs g) (==-rhs g))])
		(if (fail? g) (values fail failure 0)
		    (values g s (state-varid s))))]
     [(fresh? g) (let*-values ([(g s^ p) (g s empty-package)]
			       [(g s^ v) (simplify-constraint g s^)])
		   (if (succeed? g) (values g s (state-varid s)) (values g s^ v)))] ; If fresh purely succeeds, we don't need to save space for the new variables it created.
     [(conj? g) (let-values ([(g^ s v) (simplify-constraint (conj-car g) s)])
		  (if (fail? g^) (values fail failure 0)
		      (let-values ([(g s v) (simplify-constraint (conj-cdr g) s)])			
			(values (normalized-conj* g^ g) s v))))]
     [(disj? g) (let-values ([(g^ s^ v) (simplify-constraint (disj-car g) s)])
		  (cond
		   [(succeed? g^) (values succeed s (state-varid s))]
		   [(fail? g^) (simplify-constraint (disj-cdr g) s)]
		   [else (values (normalized-disj* g^ (disj-cdr g)) s v)]))]
     [(and (noto? g) (not (fresh? (noto-goal g))))
      (let*-values ([(g s^ v) (simplify-constraint (noto-goal g) s)]
		    [(g) (noto g)])
	(if (fail? g) (values fail failure 0)
	    (values g s (state-varid s))))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) ((noto-goal g) s empty-package)]) ; TODO find all empty packages and consider threading real package
					       (assert #f)
					       (printf "GOAL: ~s~%NOTO: ~s~%~%" g (noto g))
					       (simplify-constraint (noto g) s))]
     [(constraint? g) (simplify-constraint (constraint-goal g) s)]
     [(pconstraint? g) (values ((pconstraint-procedure g) s) s (state-varid s))]
     [else (assertion-violation 'run-constraint "Unrecognized constraint type" g)]))

  (define (run-dfs g s sub conjs)
    (assert (and (goal? g) (state? s) (pair? sub) (goal? conjs)))
    (cond
     [(==? g) (let-values ([(s g^) (unify-no-check s (==-lhs g) (==-rhs g))])
		(if (fail? g^) (values fail failure 0)
		    (values g^ s (state-varid s))))]))

  ;; constraint pulls all attributed vars into big conj. simplifies alone in state. recurse on that. if ever we pull only successes, just attribute
  
  (define (check-constraints s g)
    ;; Runs after unification to propagate new extensions through the constraint store. g is the goal representing the updates made to the substitution by the unifier.
    ;; TODO remove all firing constraints before checking any of them in case they redundantly check each other
    (assert (and (state-or-failure? s) (goal? g)))
    (cond
     [(or (failure? s) (fail? g)) failure] ; State has failed
     [(succeed? g) s] ; State has succeeded without modification     
     [(==? g) (fire-constraint s (list (==-lhs g)))] ; State has updated a single variable
     [(conj? g) (fire-constraint s (map ==-lhs (conj-conjuncts g)))] ; Updated multiple variables
     [else (assertion-violation 'check-constraints "Unrecognized constraint type" g)]))

  (define (fire-constraint s vs)
    (assert (and (state? s) (list? vs) (fold-left eq? #t (map var? vs)))) ; -> state-or-failure?

    #;
    (printf "FIRING CONSTRAINT (~s): ~s~%SUB: ~s~%STORE: ~s~%REDUCED: ~s~%DEPLETED: ~s~%STATE: ~s~%~%" (==-lhs e) (get-constraint (state-constraints s) (==-lhs e))
	    
	    (print-substitution s)
	    (map car (constraint-store-constraints (state-constraints s)))
	    (values-ref (simplify-constraint (get-constraint (state-constraints s) (==-lhs e)) (set-state-constraints s (remove-constraint (state-constraints s) (==-lhs e)))) 0)
	    (map car (constraint-store-constraints (remove-constraint (state-constraints s) (==-lhs e))))
	    (set-state-constraints s (remove-constraint (state-constraints s) (==-lhs e))))
    (run-constraint (get-constraints s vs) (remove-constraints s vs)))
  
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
	 ;;(assert (eq? (walk s v) v)) ; TODO delete this assertion
	 (state-add-constraint s v c)) s (get-attributed-vars c))]))

  (define (get-attributed-vars g)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; TODO attributed vars should probably be deduplicated
    ;; TODO attributed vars should handle (constraint)'s
    (assert (goal? g)) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (cond
     [(disj? g) (get-attributed-vars (disj-car g))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
     [(conj? g) (apply append (map get-attributed-vars (conj-conjuncts g)))]
     [(noto? g) (get-attributed-vars (noto-goal g))]
     [(==? g) (filter var? (list (==-lhs g) (==-rhs g)))]
     [(pconstraint? g) (pconstraint-vars g)]
     [else (assertion-violation 'get-attributed-vars "Unrecognized constraint type" g)]))) 
