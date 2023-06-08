(library (solver) ; Constraint solving
  (export run-constraint)
  (import (chezscheme) (state) (negation) (datatypes))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (assert (and (goal? g) (state? s))) ; -> state-or-failure?
    (call-with-values (lambda () (solve-constraint g s succeed succeed)) store-disjunctions))
  
  (define (solve-constraint g s conjs out)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (assert (and (goal? g) (state? s) (goal? conjs))) ; -> goal? state-or-failure?
    (cond
     [(fail? g) (values fail failure)]
     [(succeed? g) (if (succeed? conjs) (values out s) (solve-constraint conjs s succeed out))]
     [(==? g) (solve-== g s conjs out)]
     [(and (noto? g) (==? (noto-goal g))) (solve-=/= g s conjs out)]
     [(disj? g) (let-values ([(g s) (solve-disj g s conjs (simplification-level))])
		  (values (normalized-conj* out g) s))]
     [(conj? g) (solve-constraint (conj-car g) s (normalized-conj* (conj-cdr g) conjs) out)]
     [(constraint? g) (solve-constraint (constraint-goal g) s conjs out)]
     [(guardo? g) (solve-guardo g s conjs out)]
     [(pconstraint? g) (assert #f) (values ((pconstraint-procedure g) s) s)]
     [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)]))

  (define (solve-== g s gs out)
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    (let-values ([(g s) (unify s (==-lhs g) (==-rhs g))])
      (if (fail? g) (values fail failure)
	  (solve-constraint ; Run constraints attributed to all unified vars
	   (conj* (get-constraints s (attributed-vars g)) gs)
	   (remove-constraints s (attributed-vars g))
	   succeed (normalized-conj* out g)))))
  
  (define (solve-=/= g s conjs out)
    (let-values ([(g s^) (unify s (==-lhs (noto-goal g)) (==-rhs (noto-goal g)))]) ;TODO disunification unifier can be small step: we nly need to know 1 =/= succeeds before proceeding with search
	(cond
	 [(succeed? g) (values fail failure)]
	 [(fail? g) (solve-constraint conjs s succeed out)]
	 [else
	  #;
	  (solve-constraint ; Run constraints attributed to all unified vars
	   (conj* (get-constraints s (attributed-vars (noto g))) conjs)
	   (store-constraint (remove-constraints s (attributed-vars (noto g))) g)
	   succeed out)


	  
	  (let-values ([(g^ s) (solve-=/=* (noto g) s conjs)]) ;
	    (values (normalized-conj* out (noto g) g^) s))])))

  (define (solve-=/=* g s gs)
    (assert (and (goal? g) (or (disj? g) (noto? g)) (state? s) (goal? g))) ; -> goal? state-or-failure?
    (let* ([a-vars (attributed-vars (disj-car g))]
	   [c (get-constraints s a-vars)] ;TODO =/= may not need to fire all the constraints conjoined to a given attributed var. maybe only grab a subset with == in them somewhere
	   [c (if (may-unify c (car a-vars)) c succeed)] ; If c has no == that may fail when applied to this =/=, do not bother to apply it.
	   [s (if (succeed? c) s (remove-constraints s a-vars))]) ; If we are not applying the constraint, leave it in the store.
      (let-values ([(g0 s0) (solve-constraint c (store-constraint s (disj-car g)) gs succeed)])
	(cond
	 [(noto? g) (values g0 s0)] ; This is not a disjunction, so just modify the state and proceed.
	 [(succeed? g0) (values succeed s)] ; The head of the disjunction succeeds, so discard it.
	 [(fail? g0) (if (disj? g) (solve-=/=* (disj-cdr g) s gs) (values fail failure))] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
	 [else (values (normalized-disj* g0 (normalized-conj* (disj-cdr g) gs)) s)])))) ; The head is simplified, and since pure =/= can only fail but not collapse, return as is with 1 level of simplification.

  (define (may-unify g v)
    ;; #t if this constraint contains a == containing var v, implying that it might fail or collapse if we conjoin a =/= assigned to v.
    (cond
     [(==? g) (or (equal? (==-lhs g) v))] ; Existing constraints are already normalized, so only lhs need be checked.
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-car (disj-cdr g)) v))] ; If the disjunction has 2 disjuncts without v, it can neither fail nor collapse.
     [else #f]))
  
  (define (solve-disj g s conjs s-level)
    ;; Test as many disjuncts as needed to satisfy the desired simplification-level, and leave the rest untouched
    ;; level 1 - only worry about failing if a unification violates a constraint.
    ;; level 2 - level 1 + if we can commit to a single branch and turn a constraint into a unification, do it.
    ;; level -1 - solve all disjuncts to lowest terms.
    ;;TODO if we maintain a list of all simplified == and =/= seen in each simplified disjunct, we can keep consuming disjuncts until the list of those that have appeared in each case is empty. if we get to the end and some still appear in that case, we'll want to factor them out of the disj and apply them to the state. as an optimization, if the list of values in any state is already exactly that list, we can just reuse that state instead of reapplying them to the blank state
    (cond 
     [(fail? g) (values fail failure)]
     [(zero? s-level) (values g s)]
     [else ;TODO do we need to solve disjs that dont contain any ==? in fact, we can stop as soon as we find one such disjunct. in fact, that disjunct MUST unify if we are to care about it, so the == must be in the top level conjunction of the goal
      (let-values ([(g0 s0) (solve-constraint (disj-car g) s conjs succeed)])
	;(printf "1HEAD: ~s~%1ORIG: ~s~%" g0 g)
	(cond
	 [(succeed? g0) (values succeed s)] ; The whole disjunction is satisfied, so just drop it.
	 [(fail? g0) (solve-disj (disj-cdr g) s conjs s-level)] ; Keep going until we find a satisfiable disjunct or run out.
	 [(disj? g0) (values (normalized-disj* g0 (normalized-conj* (disj-cdr g) conjs)) s)]
	 [else ; At least one satisfiable disjunct
	  (let-values ([(g^ s^) (solve-disj (disj-car (disj-cdr g)) s conjs (- s-level 1))])
	    ;(printf "2HEAD: ~s~%2ORIG: ~s~%2BODY: ~s~%" g0 g g^)
	    (cond
	     [(succeed? g^) (values succeed s)] ; Turns out the whole disjunction succeeded, so drop everything.
	     [(fail? g^) (values g0 s0)] ; Only one disjunct succeeded, so commit to it.
	     [else (values (normalized-disj* g0 g^ (normalized-conj* (disj-cdr (disj-cdr g)) conjs)) s)]))]))])) ; Return a new, simplified disjunction.
  
  (define (solve-guardo g s conjs out)
    (let ([v (walk s (guardo-var g))])
		    (cond
		     [(var? v) (let ([g (guardo v (guardo-procedure g))])
				 (values g (store-constraint s g)))]
		     [(pair? v) (solve-constraint ((guardo-procedure g) (car v) (cdr v)) s conjs out)]
		     [else (values fail failure)])))
  
  (define (store-disjunctions g s)
    (assert (and (goal? g) (or (fail? g) (not (failure? s)))))
    ;; Because solve-constraint has already stored all simple conjoined constraints in the state, throw them away and only put disjunctions in the store.
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
