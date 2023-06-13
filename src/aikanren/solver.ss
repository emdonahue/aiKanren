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
     [(disj? g) (solve-disj g s conjs out)]
     [(conj? g) (solve-constraint (conj-car g) s (conj (conj-cdr g) conjs) out)]
     [(constraint? g) (solve-constraint (constraint-goal g) s conjs out)]
     [(guardo? g) (solve-guardo g s conjs out)]
     [(pconstraint? g)
      (assert #f)
      (values ((pconstraint-procedure g) s) s)]
     [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)]))

  (define (solve-== g s gs out)
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    (let-values ([(g s) (unify s (==-lhs g) (==-rhs g))])
      (if (fail? g) (values fail failure)
	  (solve-constraint ; Run constraints attributed to all unified vars
	   (conj (get-constraints s (attributed-vars g)) gs)
	   (remove-constraints s (attributed-vars g))
	   succeed (conj out g)))))
  
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
	    (values (conj out (conj (noto g) g^)) s))])))

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
	 [else (values (disj g0 (conj (disj-cdr g) gs)) s)])))) ; The head is simplified, and since pure =/= can only fail but not collapse, return as is with 1 level of simplification.

  (define (may-unify g v)
    ;; #t if this constraint contains a == containing var v, implying that it might fail or collapse if we conjoin a =/= assigned to v.
    (cond
     [(==? g) (or (equal? (==-lhs g) v))] ; Existing constraints are already normalized, so only lhs need be checked.
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-car (disj-cdr g)) v))] ; If the disjunction has 2 disjuncts without v, it can neither fail nor collapse.
     [else #f]))
   
  (define solve-disj
    (case-lambda
      [(g s conjs out)
       (let-values ([(g s) (solve-disj g s s conjs fail fail fail)])
	 (values (conj out g) s))]
      [(g s s^ ctn ==s lhs-disj rhs-disj)
       (assert (and (goal? g) (state? s) (goal? ctn)))
       (cond ;TODO break fail and succeed into separate cases
	[(or (succeed? ==s) (fail? g)) (values (conj ==s (disj (disj lhs-disj g) (conj rhs-disj ctn)))
					       (cond
						[(and (fail? lhs-disj) (fail? rhs-disj)) failure]
						[(or (and (fail? lhs-disj) (not (disj? rhs-disj)))
						     (and (fail? rhs-disj) (not (disj? lhs-disj)))) s^]
						[else s]))]
	[(disj? g) (solve-disj (disj-car g) s s^ ctn ==s lhs-disj (disj (disj-cdr g) rhs-disj))] ;TODO replace disj with make-disj where possible
	[else (let-values ([(g0 s0) (solve-constraint g s ctn succeed)])
		(cond
		 [(succeed? g0) (values succeed s)] ; First disjunct succeeds => entire constraint is already satisfied.
		 [(fail? g0) (solve-disj (disj-car rhs-disj) s s^ ctn ==s lhs-disj (disj-cdr rhs-disj))] ; First disjunct fails => check next disjunct.
		 [else (solve-disj (disj-car rhs-disj) s s0 ctn (diff-== ==s g0) (disj lhs-disj g0) (disj-cdr rhs-disj))]))])]))
  
  (define (diff-== a b)
    (cond
     [(fail? a) b]
     [(fail? b) a]
     [(==? a) (conj-member b a)]
     [(conj? a) (conj (diff-== (conj-car a) b) (diff-== (conj-cdr a) b))]
     [else succeed]))

  (define (conj-member c e)
    (cond
     [(equal? c e) e]
     [(conj? c) (let ([lhs (conj-member (conj-car c) e)])
		  (if (succeed? lhs) (conj-member (conj-cdr c) e) lhs))]
     [else succeed]))
  
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
       (cond
	[(succeed? g) vs]
	[(disj? g) (let-values ([(_ vs) (attributed-vars-disj g 2 vs)]) vs)] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint TODO if we are checking 2 disjuncts, do we need both attr vars?
	[(conj? g) (attributed-vars (conj-car g) (attributed-vars (conj-cdr g) vs))]
	[(noto? g) (attributed-vars (noto-goal g) vs)]
	[(==? g)
	 (assert (var? (==-lhs g)))
	 (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs))]
	[(pconstraint? g)
	 (assert #f)
	 (append (filter (lambda (v) (not (memq v vs))) (pconstraint-vars g)) vs)]
	[(guardo? g) (if (memq (guardo-var g) vs) vs (cons (guardo-var g) vs))]
	[(constraint? g) (attributed-vars (constraint-goal g) vs)]
	[else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])]))

  (define (attributed-vars-disj d num-branches vs)
    (if (disj? d)
	(let-values ([(num-remaining vs) (attributed-vars-disj (disj-lhs d) num-branches vs)])
	  (if (fx= num-remaining 0)
	      (values 0 vs)
	      (attributed-vars-disj (disj-rhs d) num-remaining vs)))
	(values (fx1- num-branches) (attributed-vars d vs))))
  
)