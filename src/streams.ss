;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus run-stream-constraint run-stream-constraint unify-check)
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
     [(conj? g) (let-values ([(xxx s p) (run-goal (conj-car g) s p)])
		  (bind (conj-cdr g) s p))]
     [(disj? g) (let*-values
		    ([(lhg lhs p) (run-goal (disj-car g) s p)]
		     [(rhg rhs p) (run-goal (disj-cdr g) s p)])
		  (values (disj* lhg rhg) (mplus lhs rhs) p))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) (g s p)])
					       (run-goal (noto g) s p))]
     [(and (noto? g) (not (fresh? (noto-goal g))))
      (let*-values ([(g s^ p) (run-goal (noto-goal g) s p)]
		    [(g) (noto g)])
	(values g (store-constraint s g) p))]
     [else (let-values ([(s p)
			 (cond     
			  
			  
			  
			  
			  
			  
			  
			  [(constraint? g) (values (run-constraint s (constraint-goal g)) p)]
			  [else (assert #f) (values 1 2)])]) (values 'run-goal-goal s p))]))

  #;(define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; ->stream? package?
    (cond     
     [(succeed? g) (values succeed s p)]
     [(fail? g) (values fail failure p)]
     [(fresh? g)
      (let-values ([(g s p) (g s p)])
	(values g (make-incomplete g s) p))]
     [(==? g)
      (let-values ([(s g) (unify s (==-lhs g) (==-rhs g))])
	(values g s p))]
     [(conj? g)
      (let-values ([(g0 s p) (run-goal (conj-car g) s p)]
		   [(g s p) (bind (conj-cdr g) s p)])
	(values (normalized-conj* g0 g) s p))]
     [(disj? g)
      (let*-values
	  ([(lhg lhs p) (run-goal (disj-car g) s p)]
	   [(rhg rhs p) (run-goal (disj-cdr g) s p)])
	(values (normalized-disj* lhg rhg) (mplus lhs rhs) p))]
     [(=/=? g) (values g (run-constraint s (noto (== (=/=-lhs g) (=/=-rhs g)))) p)]
     [(noto? g) (run-goal (noto (g s p)) s p)]
     [(constraint? g) (values g (run-constraint s (constraint-goal g)) p)]
     [else (assert #f)]))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (complete lhs rhs)]
     [(complete? lhs) (complete (complete-car lhs) (mplus rhs (complete-cdr lhs)))]
     [else (assert #f)]))

  (define (bind g s p)
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values fail failure p)]
     [(state? s) (let-values ([(g^ s p) (run-goal g s p)])
		   (values (normalized-conj* g g^) s p))]
     [(incomplete? s) (values 'bind-incomplete (make-incomplete g s) p)]
     [(complete? s)
      (let*-values
	  ([(xxx h p) (run-goal g (complete-car s) p)]
	   [(xxx r p) (bind g (complete-cdr s) p)])
	(values 'bind-complete (mplus h r) p))]
     [else (assert #f)]))

  (define (stream-constraint-step s)
    (assert (stream? s))
    (cond
     [(failure? s) s]
     
     [else (assert #f)] ))

  (define (run-stream-constraint g s0)
    (let-values ([(g s p) (run-goal g s0 empty-package)])
      (printf "CONSTRAINT: ~s~%STATE: ~s~%" g s)
      (cond
       [(fail? g) failure]
       [(succeed? g) s0]
       [(state? s) s]
       [(disj? g) (store-constraint s0 g)] ; TODO increase the var-id counter
       [else (assert #f)])))
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p))) ; ->stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values failure p)]
     [(incomplete? s)
      (let-values ([(g s p) (run-goal (incomplete-goal s) (incomplete-state s) p)])
	(values s p))]
     [(mplus? s) (let-values ([(s p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) s) p))]
     [(complete? s) (values (complete-cdr s) p)]
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
      (printf "")
      (store-constraint s g)))
  
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
     [(disj? c) (values s (normalized-disj* c (disj gs)))]
     [(null? gs) (values (if (==? c) ==-s s) c)] ; If committing to a single ==, reuse the substitution.
     [else (let-values ([(s^ g) (run-simple-constraint s (car gs))])
	     (run-disj s (cdr gs) (normalized-disj (list c g))
		       (if (and #f (==? (car gs)) (not (fail? g))) s^ ==-s)))]))

  (define (run-simple-constraint s g)
    (assert (and (state-or-failure? s) (goal? g))) ; -> state? goal?
    (cond
     [(or (failure? s) (fail? g)) (values failure g)]
     [(succeed? g) (values s g)]
     [(==? g) (unify-check s (==-lhs g) (==-rhs g))]
     [(noto? g) (values s (noto (values-ref (unify-check s (==-lhs (noto-goal g)) (==-rhs (noto-goal g))) 1)))]
     [(fresh? g) (run-simple-constraint s (first-value (g s empty-package)))]
     [(conj? g) (run-conj s (conj-conjuncts g) succeed)]
     [(disj? g) (run-disj s (disj-disjuncts g) fail failure)]
     [(constraint? g) (run-simple-constraint s (constraint-goal g))]
     [else (assert #f)]))

  (define (get-attributed-vars c)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; TODO attributed vars should probably be deduplicated    
    (assert (not (conj? c))) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (cond
     [(disj? c) (get-attributed-vars (disj-car c))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
     [(noto? c) (get-attributed-vars (noto-goal c))]
     [else (filter var? (vector->list c))]))
  
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

  ) 
