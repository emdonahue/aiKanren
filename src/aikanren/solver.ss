(library (solver) ; Constraint solving
  (export run-constraint)
  (import (chezscheme) (state) (negation) (datatypes) (utils))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (assert (and (goal? g) (state-or-failure? s))) ; -> state-or-failure?
    (call-with-values (lambda () (solve-constraint g s succeed succeed)) store-disjunctions))
  
  (define (solve-constraint g s conjs out)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (assert (and (goal? g) (state-or-failure? s) (goal? conjs))) ; -> goal? state-or-failure?
    (exclusive-cond
     [(fail? g) (values fail failure)]
     [(succeed? g) (if (succeed? conjs) (values out s) (solve-constraint conjs s succeed out))]
     [(==? g) (solve-== g s conjs out)]
     [(noto? g) (solve-noto (noto-goal g) s conjs out)]
     [(disj? g) (solve-disjunction g s conjs out)]
     [(conde? g) (solve-constraint (conde->disj g) s conjs out)]
     [(conj? g) (solve-constraint (conj-car g) s (conj (conj-cdr g) conjs) out)]
     [(constraint? g) (solve-constraint (constraint-goal g) s conjs out)]
     [(guardo? g) (solve-guardo g s conjs out)]
     [(fresh? g) (let-values ([(g s p) (g s empty-package)])
		   (solve-constraint g s conjs out))]
     [(matcho? g) (solve-matcho g s conjs out)]
     [(pconstraint? g) (solve-pconstraint g s conjs out)]
     [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)]))

  (define (solve-noto g s ctn out)
    (if (==? g) (solve-=/= g s ctn out)
	(let-values ([(g s^) (solve-constraint g s succeed out)])
	  (let ([g (noto g)])
	    (if (fail? g) (values fail failure)
		(solve-constraint ctn (store-constraint s g) succeed (conj out g)))))))
  
  (define (solve-== g s gs out)
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    ;;TODO quick replace extended vars in constraints looked up during unify and check for immediate failures
    ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
    (let-values ([(g s) (unify s (==-lhs g) (==-rhs g))])
      (if (fail? g) (values fail failure)
	  (solve-constraint ; Run constraints attributed to all unified vars
	   (conj (get-constraints s (attributed-vars g)) gs)
	   (remove-constraints s (attributed-vars g))
	   succeed (conj out g)))))


  
  (define (solve-=/= g s ctn out)   
    (let ([g (disunify s (==-lhs g) (==-rhs g))])
      (assert (goal? g))
      (exclusive-cond
       [(fail? g) (values fail failure)]
       [(succeed? g) (solve-constraint ctn s succeed out)]
       [else
	(let* ([a-vars (attributed-vars (disj-car g))] ; Disequalities only have one attributed var.
	       [c (get-constraints s a-vars)] ;TODO =/= may not need to fire all the constraints conjoined to a given attributed var. maybe only grab a subset with == in them somewhere. However, these may nevertheless trigger unification on that var
	       [c (if (may-unify c (car a-vars)) c succeed)] ; If c has no == that may fail when applied to this =/=, do not bother to apply it.
	       [s (if (succeed? c) s (remove-constraints s a-vars))]) ; If we are not applying the constraint, leave it in the store.
	  (let-values ([(g0 s0) (solve-constraint c (store-constraint s (disj-car g)) ctn succeed)]) ; Evaluate constraints with the first disequality in the store.
	    (cond ;TODO check noto after succ/fail
	     [(noto? g) (values (conj out (conj g g0)) s0)] ; This is not a disjunction, so just modify the state and proceed.
	     [(succeed? g0) (values (conj g out) s)] ; The head of the disjunction succeeds, so discard it.
	     ;;TODO let solve constraint handle fail case
	     [(fail? g0) (if (disj? g) (solve-constraint (disj-cdr g) s ctn out) (values fail failure))] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
	     [else (values (conj out (conj (disj-car g) (disj g0 (conj (disj-cdr g) ctn)))) s)])

	    #;
	    	  (let-values ([(g^ s) (solve-=/=* (noto g) s ctn)])
		    (values (conj out (conj (noto g) g^)) s))))])))
  
  #;
  (define (solve-=/= g s ctn out)   
    (let-values ([(g s^) (unify s (==-lhs g) (==-rhs g))]) ;TODO disunification unifier can be small step: we nly need to know 1 =/= succeeds before proceeding with search
      (exclusive-cond
       [(succeed? g) (values fail failure)]
       [(fail? g) (solve-constraint ctn s succeed out)]
       [else
	(let* ([a-vars (attributed-vars (disj-car g))]
	       [c (get-constraints s a-vars)] ;TODO =/= may not need to fire all the constraints conjoined to a given attributed var. maybe only grab a subset with == in them somewhere. However, these may nevertheless trigger unification on that var
	       [c (if (may-unify c (car a-vars)) c succeed)] ; If c has no == that may fail when applied to this =/=, do not bother to apply it.
	       [s^ (if (succeed? c) s (remove-constraints s a-vars))]) ; If we are not applying the constraint, leave it in the store.
	  (let-values ([(g0 s0) (solve-constraint c (store-constraint s^ (disj-car (noto g))) ctn succeed)])
	    (let* ([g (noto g)]
		   [s s^])
	     (cond
	      [(noto? g) (values (conj out (conj g g0)) s0)] ; This is not a disjunction, so just modify the state and proceed.
	      [(succeed? g0) (values (conj g out) s)] ; The head of the disjunction succeeds, so discard it.
	      [(fail? g0) (if (disj? g) (solve-=/= (disj-cdr g) s ctn out) (values fail failure))] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
	      [else (values (conj out (conj (disj-car g) (disj g0 (conj (disj-cdr g) ctn)))) s)]))

	    #;
	    	  (let-values ([(g^ s) (solve-=/=* (noto g) s ctn)])
		    (values (conj out (conj (noto g) g^)) s))))])))

  #;
  (define (solve-=/=* g s gs) ;;TODO remove solve-=/=*
    (assert (and (goal? g) (or (disj? g) (noto? g)) (state? s) (goal? g))) ; -> goal? state-or-failure?
    (let* ([a-vars (attributed-vars (disj-car g))]
	   [c (get-constraints s a-vars)] ;TODO =/= may not need to fire all the constraints conjoined to a given attributed var. maybe only grab a subset with == in them somewhere. However, these may nevertheless trigger unification on that var
	   [c (if (may-unify c (car a-vars)) c succeed)] ; If c has no == that may fail when applied to this =/=, do not bother to apply it.
	   [s (if (succeed? c) s (remove-constraints s a-vars))]) ; If we are not applying the constraint, leave it in the store.
      (let-values ([(g0 s0) (solve-constraint c (store-constraint s (disj-car g)) gs succeed)])
	(cond
	 [(noto? g) (values g0 s0)] ; This is not a disjunction, so just modify the state and proceed.
	 [(succeed? g0) (values succeed s)] ; The head of the disjunction succeeds, so discard it.
	 [(fail? g0) (if (disj? g) (solve-=/=* (disj-cdr g) s gs) (values fail failure))] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
	 [else (values (disj g0 (conj (disj-cdr g) gs)) s)])))) ; The head is simplified, and since pure =/= can only fail but not collapse, return as is with 1 level of simplification.

  (define (may-unify g v)
    ;; #t if this constraint contains a == containing var v, implying that it might fail or collapse if we conjoin a =/= assigned to v.
    (exclusive-cond
     [(==? g) (or (equal? (==-lhs g) v))] ; Existing constraints are already normalized, so only lhs need be checked.
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-car (disj-cdr g)) v))] ; If the disjunction has 2 disjuncts without v, it can neither fail nor collapse.
     [else #f]))

  (define (solve-matcho g s ctn out)
    (if (null? (matcho-out-vars g))
	(let-values ([(_ g s p) (expand-matcho g s empty-package)])
	  (solve-constraint g s ctn out))
	(let ([v (walk s (car (matcho-out-vars g)))]) ;TODO this walk should be handled by == when it replaces var with new binding
	  ;(printf "walked ~s to ~s~%" (car (matcho-out-vars g)) v)
	  (if (var? v)
	      (let ([m (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g))])
		(solve-constraint ctn (store-constraint s m) succeed (conj out m)))
	      (solve-matcho (make-matcho (cdr (matcho-out-vars g)) (matcho-in-vars g) (matcho-goal g)) s ctn out))))) ;TODO just operate on the list for matcho solving

  (define (solve-disjunction g s ctn out)
    (let-values ([(g s) (solve-disj g s ctn fail)])
	 (values (conj out g) s)))
  
  (define (solve-disj g s ctn ==s) ;TODO delete extracted == from disj clauses
    (assert (and (goal? g) (state? s) (goal? ctn)))
    (exclusive-cond
     [(fail? g) (values fail failure)] ; No more disjuncts to analyze.
     [(succeed? ==s) (values (conj g ctn) s)] ; No unifications made in all branches. Suspend early.
     [else (let-values ([(g0 s0) (solve-constraint (disj-car g) s ctn succeed)])
	     (exclusive-cond
	      [(succeed? g0) (values succeed s)] ; First disjunct succeeds => entire constraint is already satisfied.
	      [(fail? g0) (solve-disj (disj-cdr g) s ctn ==s)] ; First disjunct fails => check next disjunct.
	      [(disj? g0) (values (disj g0 (make-conj (disj-cdr g) ctn)) s)] ; First disjunct itself a disjunction => whole disjunction not reducible.
	      [else
	       (let-values ([(g s^) (solve-disj (disj-cdr g) s ctn (diff-== ==s g0))])
		 (exclusive-cond
		  [(fail? g) (values g0 s0)]
		  [(succeed? g) (values succeed s)]
		  [else (values (make-disj g0 g) s)]))]))]))
  
  (define (diff-== ==s g) ;TODO make diff-== just a list. no need to dedup because we are dredging normalized output
    (cond ; TODO succeed should probably skip any computations in diff-==
     [(fail? ==s) (conj-filter g ==?)] ; ==s starts as fail, so at the beginning we want to filter out the initial ==s.
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
  
  (define (solve-guardo g s conjs out)
    (let ([v (walk s (guardo-var g))])
		    (exclusive-cond
		     [(var? v) (let ([g (guardo v (guardo-procedure g))])
				 (values g (store-constraint s g)))]
		     [(pair? v) (solve-constraint ((guardo-procedure g) (car v) (cdr v)) s conjs out)]
		     [else (values fail failure)])))

  (define (solve-pconstraint g s ctn out)
		(let ([g ((pconstraint-procedure g) s)])
		  (exclusive-cond
		   [(succeed? g) (values succeed s)]
		   [(fail? g) (values fail failure)]
		   [else (solve-constraint ctn (store-constraint s g) succeed (conj out g))])))
  
  (define (store-disjunctions g s)
    (assert (and (goal? g) (or (fail? g) (not (failure? s)))))
    ;; Because solve-constraint has already stored all simple conjoined constraints in the state, throw them away and only put disjunctions in the store.
    (exclusive-cond
     [(conj? g) (store-disjunctions (conj-cdr g) (store-disjunctions (conj-car g) s))]
     [(disj? g) (store-constraint s g)]
     [else s]))

  (define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state? s) (assert (or (guardo? g) (matcho? g) (noto? g) (disj? g) (pconstraint? g) (succeed? g) (fail? g))))) ; -> state?
    (exclusive-cond
     [(succeed? g) s]
     [(fail? g) failure]
     [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))] ;TODO consider reversing constraint storage to put old constraints first
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
  
  (define attributed-vars
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (case-lambda
      [(g) (attributed-vars g '())]
      [(g vs)
       ;; TODO optimize which disj constraint we pick for attribution to minimize free vars
       (assert (goal? g))
       (exclusive-cond
	[(succeed? g) vs]
	[(disj? g) (attributed-vars-disj g vs)] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint TODO if we are checking 2 disjuncts, do we need both attr vars?
	[(conj? g) (attributed-vars (conj-car g) (attributed-vars (conj-cdr g) vs))]
	[(noto? g) (attributed-vars (noto-goal g) vs)]
	[(==? g)
	 (assert (var? (==-lhs g)))
	 (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs))]
	[(matcho? g)
	 (if (or (null? (matcho-out-vars g)) (memq (car (matcho-out-vars g)) vs)) vs (cons (car (matcho-out-vars g)) vs))]
	[(pconstraint? g)
	 (append (filter (lambda (v) (not (memq v vs))) (pconstraint-vars g)) vs)]
	[(guardo? g) (if (memq (guardo-var g) vs) vs (cons (guardo-var g) vs))]
	[(constraint? g) (attributed-vars (constraint-goal g) vs)]
	[else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])]))

  (define (attributed-vars-disj d vs)
    (if (maybe-==? (disj-car d))
	(attributed-vars (disj-car d) (attributed-vars (disj-car (disj-cdr d)) vs))
	(attributed-vars (disj-car d) vs)))

    (define (maybe-==? g)
    ;; True if a goal might imply a extension of the substitution.
    (assert (not (or (succeed? g) (fail? g) (disj? g))))
    (exclusive-cond
     [(conj? g) (or (maybe-==? (conj-car g)) (maybe-==? (conj-cdr g)))]
     [(noto? g) #f]
     [(constraint? g) (maybe-==? (constraint-goal g))]
     [else #t])))
