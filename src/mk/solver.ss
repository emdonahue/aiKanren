(library (solver) ; Constraint solving
  (export run-constraint)
  (import (chezscheme) (state) (negation) (datatypes) (utils))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (assert (and (goal? g) (state-or-failure? s))) ; -> state-or-failure?
    (call-with-values (lambda () (solve-constraint g s succeed succeed)) store-disjunctions))
  
  (org-define (solve-constraint g s conjs out)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (assert (and (goal? g) (state-or-failure? s) (goal? conjs))) ; -> goal? state-or-failure?
    (exclusive-cond
     [(fail? g) (values fail failure)]
     [(succeed? g) (if (succeed? conjs) (values out s) (solve-constraint conjs s succeed out))]
     [(==? g) (solve-== g s conjs out)]
     [(noto? g) (solve-noto (noto-goal g) s conjs out)]
     [(disj? g) (solve-disj g s conjs out)]
     [(conde? g) (solve-constraint (conde->disj g) s conjs out)]
     [(conj? g) (solve-constraint (conj-car g) s (conj (conj-cdr g) conjs) out)]
     [(constraint? g) (solve-constraint (constraint-goal g) s conjs out)]
     [(guardo? g) (solve-guardo g s conjs out)]
     [(fresh? g) (let-values ([(g s p) (g s empty-package)])
		   (solve-constraint g s conjs out))]
     [(matcho? g) (solve-matcho g s conjs out)]
     [(pconstraint? g) (solve-pconstraint g s conjs out)]
     [(trace-goal? g) (run-constraint (trace-goal-goal g) s)]
     [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)]))

  (define (solve-noto g s ctn out)
    (if (==? g) (solve-=/= g s ctn out)
	(let-values ([(g s^) (solve-constraint g s succeed out)])
	  (let ([g (noto g)])
	    (if (fail? g) (values fail failure)
		(solve-constraint ctn (store-constraint s g) succeed (conj out g)))))))
  
  (define (solve-== g s ctn out)
    ;; Runs a unification, collects constraints that need to be rechecked as a result of unification, and solves those constraints.
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    ;;TODO quick replace extended vars in constraints looked up during unify and check for immediate failures
    ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
    ;; todo can we sort our conjunctions into those containing variables not touched by the current unifications and so may need to be further walked/solved and those that we can just directly strap on to the out parameter now? may have to do with analyzing which ones have disjunctions that are still normalized even after updates with current unifications
    (let-values ([(g c s) (unify s (==-lhs g) (==-rhs g))]) ; g is the conjunction of normalized unifications made. c is the conjunction of constraints that need to be rechecked.
      (assert (goal? c))
      (if (or (fail? g) (occurs-check* g s)) (values fail failure)
	  (solve-constraint c s ctn (conj out g)))))

  (org-define (occurs-check* g s) ; TODO add a non occurs check =!= or ==!
    (cert (or (conj? g) (==? g) (succeed? g)))
    (exclusive-cond
     [(conj? g) (and (occurs-check* (conj-lhs g) s) (occurs-check* (conj-rhs g) s))]
     [(succeed? g) #f]
     [else (occurs-check s (==-lhs g) (==-rhs g))]))

  (org-define (occurs-check s v term) ;TODO see if the normalized ==s can help speed up occurs-check, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification?
	      (cert (state? s) (var? v))
	      (exclusive-cond
	       [(eq? v term) #t] ; term is already walked by normalized ==s
	       [(pair? term)
		(or (eq? v (car term)) (eq? v (cdr term)) ; can't just walk a term bc it is already in the substitution
		 (occurs-check s v (walk-var s (car term))) (occurs-check s v (walk-var s (cdr term))))]
	       [else #f]))
  
  (define (solve-=/= g s ctn out)   
    (let-values ([(g c s) (disunify s (==-lhs g) (==-rhs g))])
      (exclusive-cond
       [(fail? g) (values fail failure)]
       [(succeed? g) (solve-constraint ctn s succeed out)]
       [else
	  (let-values ([(g0 s0) (solve-constraint c (store-constraint s (disj-car g)) ctn succeed)]) ; Evaluate constraints with the first disequality in the store.
	    (if (noto? g) (values (conj out (conj g g0)) s0) ; This is not a disjunction, so just modify the state and proceed with whatever the value. 
		(exclusive-cond
		 [(succeed? g0) (values (conj g out) s)] ; The constraints on the attributed vars are trivial, so simply return the entire disjunction and the unmodified state.
		 ;;TODO let solve constraint handle fail case
		 [(fail? g0) (solve-constraint (disj-cdr g) s ctn out)] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
		 ;; To suspend a disjunction, conjoin the output var, the head of the disjunction that has already been simplified, and a disjunction of the constraints on the head attributed vars with the continuation bound to the tail of the disjunction.
		 ;; TODO potential opportunity to store the whole disjunction instead of just the head and reuse the state if =/= is the top level disjunction
		 [else (values (conj out (conj (disj-car g) (disj g0 (conj (disj-cdr g) ctn)))) s)])))])))

  (define (solve-matcho g s ctn out)
    (if (null? (matcho-out-vars g)) ; Expand matcho immediately if all vars are ground
	(let-values ([(_ g s p) (expand-matcho g s empty-package)])
	  (solve-constraint g s ctn out)) ;TODO replace walkvar in matcho solver with walk once matcho handles walks
	(let ([v (walk-var s (car (matcho-out-vars g)))]) ;TODO this walk should be handled by == when it replaces var with new binding
	  ;;TODO if we get a non pair, we can fail matcho right away without expanding lambda
	  (if (var? v) ; If first out-var is free,
	      (let ([m (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g))]) ; store the matcho. 
		(solve-constraint ctn (store-constraint s m) succeed (conj out m))) ; Otherwise, keep looking for a free var.
	      ;;TODO just operate on the list for matcho solving
	      (solve-matcho (make-matcho (cdr (matcho-out-vars g)) (cons v (matcho-in-vars g)) (matcho-goal g)) s ctn out)))))

  (define (solve-disj g s ctn out)
    (let-values ([(head-disj g s) (solve-disj* g s ctn fail fail)]) ; The head disjunct is the first that does not unify vars common to previous disjuncts, or fail if all share at least one ==.
      (cert (goal? head-disj))
      (values (conj out (disj head-disj g)) s)))
  
  (org-define (solve-disj* g s ctn ==s parent-disj) ;TODO delete extracted == from disj clauses
    (assert (and (goal? g) (state? s) (goal? ctn)))
    (org-exclusive-cond base-case-cond
     [(fail? g) (values fail fail failure)] ; Base case: no more disjuncts to analyze. Failure produced by disj-cdr on a non-disj?.
     [else (let-values ([(g0 s0) (solve-constraint (disj-car g) s ctn succeed)])
	     (org-exclusive-cond disj-head-cond
	      [(succeed? g0) (values succeed succeed s)] ; First disjunct succeeds => entire constraint is already satisfied.
	      [(fail? g0) (solve-disj* (disj-cdr g) s ctn ==s parent-disj)] ; First disjunct fails => check next disjunct.
	      ;;TODO do we have to continue to check ==s if the returned disj might commit?
	      [(disj? g0) (values (disj-car g0) (disj (disj-cdr g0) (make-conj (disj-cdr g) ctn)) s)] ; First disjunct itself a disjunction => whole disjunction not reducible otherwise that disjunction would have normalized to a non-disjunction.
	      [else
	       (let ([==s (diff-== ==s g0)])
		 (if (succeed? ==s)
		     (if (disj? g)
			 (values (disj-car g0) (disj (disj-cdr g0) (conj (disj-cdr g) ctn)) s)
			 (values g0 fail s0))
		  (let-values ([(head-disj g s^) (solve-disj* (disj-cdr g) s ctn ==s g0)])
		    (org-exclusive-cond disj-tail-cond
		     [(and (fail? g) (fail? head-disj)) (values fail g0 s0)]
		     [(succeed? g) (values succeed succeed s)]
		     [else (values head-disj (disj g0 g) s)]))))]))]))
#;
(let ([==s (diff-== ==s g0)])
		      (if (succeed? ==s )
		       (let-values ([(g s^) (solve-disj* (disj-cdr g) s ctn ==s)])
			 (exclusive-cond
			  [(fail? g) (values g0 s0)]
			  [(succeed? g) (values succeed s)]
			  [else (values (make-disj g0 g) s)]))))
  
  (define (diff-== ==s g) ;TODO make diff-== just a list. no need to dedup because we are dredging normalized output
    (cond ; TODO succeed should probably skip any computations in diff-==
     [(fail? ==s) (conj-filter g ==?)] ; ==s starts as fail, so at the beginning we want to filter out the initial ==s. TODO instead of filtering out ==s in disj, subgoals should return them automatically as a starting point.
     [(fail? g) ==s] ; A failed goal has no bearing on the ==s common to succeeding goals.
     [(==? ==s) (if (fail? g) ==s (conj-member g ==s))]
     [(conj? ==s) (conj (diff-== (conj-car ==s) g) (diff-== (conj-cdr ==s) g))]
     [else succeed]))

  (define (conj-member c e)
    (cond
     [(equal? c e) e]
     [(conj? c) (let ([lhs (conj-member (conj-car c) e)])
		  (if (succeed? lhs) (conj-member (conj-cdr c) e) lhs))]
     [else succeed]))
  
  (define (solve-guardo g s conjs out) ;TODO remove guardo
    (let ([v (walk s (guardo-var g))])
      (exclusive-cond
       [(var? v) (let ([g (guardo v (guardo-procedure g))])
		   (values g (store-constraint s g)))]
       [(pair? v) (solve-constraint ((guardo-procedure g) (car v) (cdr v)) s conjs out)]
       [else (values fail failure)])))

  (define (solve-pconstraint g s ctn out) ; TODO add guard rails for pconstraints returning lowest form and further solving
    (assert (pconstraint? g))
    (let ([g (fold-left (lambda (g v)
			  (if (pconstraint? g)
			      (let ([walked (walk s v)])
				(if (eq? v walked) g ((pconstraint-procedure g) v walked))) g))
		      g (pconstraint-vars g))])
      (solve-constraint ctn (store-constraint s g) succeed (conj out g)))
    #;
    (let ([v (walk s (car (pconstraint-vars g)))])
    )
    #;
    (let ([g ((pconstraint-procedure g) s)])
		  (exclusive-cond
		   [(succeed? g) (values succeed s)]
		   [(fail? g) (values fail failure)]
		   [else (solve-constraint ctn (store-constraint s g) succeed (conj out g))])))
  
  (org-define (store-disjunctions g s)
    (assert (and (goal? g) (or (fail? g) (not (failure? s)))))
    ;; Because solve-constraint has already stored all simple conjoined constraints in the state, throw them away and only put disjunctions in the store.
    (exclusive-cond
     [(conj? g) (store-disjunctions (conj-cdr g) (store-disjunctions (conj-car g) s))]
     [(disj? g) (store-constraint s g)]
     [else s]))

  (org-define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state? s) (goal? g) (not (conde? g)))) ; -> state?
    (exclusive-cond
     [(succeed? g) s]
     [(fail? g) failure]
     [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s g (attributed-vars g))]))

  (define (invert-disj ds) ds) ;TODO reevaluate inverting disj given that they are now binary
  #;
  (define (invert-disj ds)
    ;;TODO perhaps instead of a fully inverted disj constraint pair we can simply add a dummy proxy constraint that if looked up succeeds but raises the constraint waiting on the original vars
    (let ([rest (disj-cdr ds)])
      (if (disj? rest)
	  (disj* (disj-car rest) (disj-car ds) (disj-cdr rest))
	  (disj rest (disj-car ds)))))
  
  (define attributed-vars ;TODO thread trace-goal through other critical infrastructure so its semantically transparent
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (case-lambda ;TODO create a defrel that encodes context information about what vars were available for use in reasoning about which freshes might be able to unify them within their lexical scope
      [(g) (let-values ([(vs unifies) (attributed-vars g '() #f)]) vs)]
      [(g vs unifies)
       (assert (goal? g))
       (exclusive-cond
	[(succeed? g) (values vs unifies)]
	[(disj? g) (let-values ([(lhs lhs-unifies) (attributed-vars (disj-car g) vs unifies)])
		     (if lhs-unifies ; Disjunct 2 normalized iff 1 contains no ==
			 (attributed-vars (disj-car (disj-cdr g)) lhs #t)
			 (values lhs unifies)))] 
	[(conj? g) (call-with-values
		       (lambda () (attributed-vars (conj-cdr g) vs unifies))
		     (lambda (vs unifies) (attributed-vars (conj-car g) vs unifies)))]
	[(noto? g) (let-values ([(vars _) (attributed-vars (noto-goal g) vs #f)])
		     (values vars unifies))]
	[(==? g)
	 (assert (var? (==-lhs g)))
	 (values (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs)) #t)]
	[(matcho? g)
	 (values (if (or (null? (matcho-out-vars g)) (memq (car (matcho-out-vars g)) vs)) vs (cons (car (matcho-out-vars g)) vs)) unifies)]
	[(pconstraint? g)
	 (values (fold-left (lambda (vs v) (if (memq v vs) vs (cons v vs))) vs (pconstraint-vars g)) unifies)]
	[(guardo? g) (values (if (memq (guardo-var g) vs) vs (cons (guardo-var g) vs)) unifies)]
	[(constraint? g) (attributed-vars (constraint-goal g) vs unifies)]
	[else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])])))
