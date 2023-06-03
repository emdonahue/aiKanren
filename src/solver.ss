(library (solver) ; Constraint solving
  (export run-constraint)
  (import (chezscheme) (state) (negation) (datatypes))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (assert (and (goal? g) (state? s))) ; -> state-or-failure?
    (call-with-values (lambda () (simplify-constraint g s succeed succeed)) store-disjunctions))
  
  (define (simplify-constraint g s conjs out)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (assert (and (goal? g) (state? s) (goal? conjs))) ; -> goal? state-or-failure?
    (cond
     [(fail? g) (values fail failure)]
     [(succeed? g) (if (succeed? conjs) (values out s) (simplify-constraint conjs s succeed out))]
     [(==? g) (simplify-== g s conjs out)]
     [(and (noto? g) (==? (noto-goal g))) (simplify-=/= g s conjs out)]
     [(disj? g) (let-values ([(g s) (simplify-disj g s conjs (simplification-level))])
		  (values (normalized-conj* out g) s))]
     [(conj? g) (simplify-constraint (conj-car g) s (normalized-conj* (conj-cdr g) conjs) out)]
     [(constraint? g) (simplify-constraint (constraint-goal g) s conjs out)]
     [(guardo? g) (simplify-guardo g s conjs out)]
     [(pconstraint? g) (assert #f) (values ((pconstraint-procedure g) s) s)]
     [else (assertion-violation 'simplify-constraint "Unrecognized constraint type" g)]))

  (define (simplify-== g s conjs out)
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    (let-values ([(g s) (unify s (==-lhs g) (==-rhs g))])
      (if (fail? g) (values fail failure)
	  (simplify-constraint ; Run constraints attributed to all unified vars
	   (conj* (get-constraints s (attributed-vars g)) conjs)
	   (remove-constraints s (attributed-vars g))
	   succeed (normalized-conj* out g)))))
  
  (define (simplify-=/= g s conjs out)
    (let-values ([(g s^) (unify s (==-lhs (noto-goal g)) (==-rhs (noto-goal g)))]) ;TODO disunification unifier can be small step: we only need to know 1 =/= succeeds before proceeding with search
	(cond
	 [(succeed? g) (values fail failure)]
	 [(fail? g) (simplify-constraint conjs s succeed out)]
	 [(==? g)
	  #;
	  (let* ([c (get-constraints s (attributed-vars g))]
			 [not-g (noto g)]
			 [out (normalized-conj* out not-g)])
		   (if (may-unify c (car (attributed-vars g))) ; Only fire constraints on the attributed var of the =/= if there is a chance they might try to unify it and thereby conflict with the =/= and possibly cancel a disjunct and arrive at a pure ==.
		       (simplify-constraint (conj* c conjs)
					    (store-constraint (remove-constraints s (attributed-vars g)) not-g)
					    succeed out)
		       (simplify-constraint conjs (store-constraint s not-g) succeed out)))
	  ;(simplify-=/=-disj g s conjs out)
	  
	  (let-values ([(g^ s) (simplify-=/=-disj g s conjs out)])
	    (values (normalized-conj* g^ (noto g)) s))]
	 [else ; Disjunction of =/=. TODO disj of =/= this cancel if the vars are different?
	  (let ([not-g (noto g)])
	    (simplify-constraint conjs
				 (store-constraint
				  (store-constraint s not-g)
				  (normalized-disj* (disj-cdr not-g) (disj-car not-g)))
				 succeed
				 (normalized-conj* out not-g)))])))

  (define (simplify-=/=-disj g s conjs out)
    (let-values ([(g^ s) 
		  (let* ([c (get-constraints s (attributed-vars g))]
			 [not-g (noto g)]
			 #;
			 [out (normalized-conj* out not-g)])
		    (if (may-unify c (car (attributed-vars g))) ; Only fire constraints on the attributed var of the =/= if there is a chance they might try to unify it and thereby conflict with the =/= and possibly cancel a disjunct and arrive at a pure ==.
			(simplify-constraint (conj* c conjs)
					     (store-constraint (remove-constraints s (attributed-vars g)) not-g)
					     succeed out)
			(simplify-constraint conjs (store-constraint s not-g) succeed out)))])
      (values g^ s))

    #;
    (let* ([c (get-constraints s (attributed-vars g))]
			[not-g (noto g)])
		   (if (may-unify c (car (attributed-vars g))) ; Only fire constraints on the attributed var of the =/= if there is a chance they might try to unify it and thereby conflict with the =/= and possibly cancel a disjunct and arrive at a pure ==.
		       (simplify-constraint (conj* c conjs)
					    (store-constraint (remove-constraints s (attributed-vars g)) not-g)
					    succeed succeed)
		       (simplify-constraint conjs (store-constraint s not-g) succeed succeed))))

  (define (simplify-disj g s conjs s-level)
    ;; Test as many disjuncts as needed to satisfy the desired simplification-level, and leave the rest untouched
    ;; level 1 - only worry about failing if a unification violates a constraint.
    ;; level 2 - level 1 + if we can commit to a single branch and turn a constraint into a unification, do it.
    ;; level -1 - simplify all disjuncts to lowest terms.
    (cond 
     [(fail? g) (values fail failure)]
     [(zero? s-level) (values g s)]
     [else ;TODO do we need to simplify disjs that dont contain any ==?
      (let-values ([(g0 s0) (simplify-constraint (disj-car g) s conjs succeed)])
	(cond
	 [(succeed? g0) (values succeed s)] ; The whole disjunction is satisfied, so just drop it.
	 [(fail? g0) (simplify-disj (disj-cdr g) s conjs s-level)] ; Keep going until we find a satisfiable disjunct or run out.
	 [else ; At least one satisfiable disjunct
	  (let-values ([(g^ s^) (simplify-disj (disj-cdr g) s conjs (- s-level 1))])
	    (cond
	     [(succeed? g^) (values succeed s)] ; Turns out the whole disjunction succeeded, so drop everything.
	     [(fail? g^) (values g0 s0)] ; Only one disjunct succeeded, so commit to it.
	     [else (values (normalized-disj* g0 g^) s)]))]))])) ; Return a new, simplified disjunction.
  
  (define (simplify-guardo g s conjs out)
    (let ([v (walk s (guardo-var g))])
		    (cond
		     [(var? v) (let ([g (guardo v (guardo-procedure g))])
				 (values g (store-constraint s g)))]
		     [(pair? v) (simplify-constraint ((guardo-procedure g) (car v) (cdr v)) s conjs out)]
		     [else (values fail failure)])))
  
  (define (may-unify g v)
    (cond
     [(==? g) (or (equal? (==-lhs g) v) (equal? (==-rhs g) v))]
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-cdr g) v))]
     [else #f]))
  
  (define (store-disjunctions g s)
    (assert (and (goal? g) (or (fail? g) (not (failure? s)))))
    ;; Because simplify-constraint has already stored all simple conjoined constraints in the state, throw them away and only put disjunctions in the store.
    (cond
     [(conj? g) (store-disjunctions (conj-cdr g) (store-disjunctions (conj-car g) s))]
     [(disj? g) (store-constraint s g)]
     [else s]))

  (define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state? s) (assert (or (guardo? g) (noto? g) (disj? g))))) ; -> state?
    (cond
     [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))]
     [(disj? g) (let* ([vars1 (attributed-vars g)]
		       [vars2 (remp (lambda (v) (memq v vars1)) (attributed-vars (disj-cdr g)))]) ;TODO be more specific about how many disjuncts we need attr vars from
		  (state-add-constraint (state-add-constraint s (invert-disj g) vars2) g vars1))]
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s g (attributed-vars g))]))

  (define (invert-disj ds)
    ;;TODO perhaps instead of a fully inverted disj constraint pair we can simply add a dummy proxy constraint that if looked up succeeds but raises the constraint waiting on the original vars
    (let ([rest (disj-cdr ds)])
      (if (disj? rest)
	  (normalized-disj* (disj-car rest) (disj-car ds) (disj-cdr rest))
	  (normalized-disj* rest (disj-car ds)))))
  
  (define (attributed-vars g)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (fold-right (lambda (v vs) (if (memq v vs) vs (cons v vs))) '() (non-unique-attributed-vars g)))
  
  (define (non-unique-attributed-vars g)    
    ;; TODO optimize which constraint we pick to minimize free vars
    (assert (goal? g))
    (cond
     [(succeed? g) '()]
     [(disj? g) (attributed-vars (disj-car g))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint TODO if we are checking 2 disjuncts, do we need both attr vars?
     [(conj? g) (apply append (map attributed-vars (conj-conjuncts g)))]
     [(noto? g) (attributed-vars (noto-goal g))]
     [(==? g) (assert (var? (==-lhs g))) (list (==-lhs g))]
     [(pconstraint? g) (pconstraint-vars g)]
     [(guardo? g) (list (guardo-var g))]
     [(constraint? g) (attributed-vars (constraint-goal g))]
     [else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)]))
  
)
