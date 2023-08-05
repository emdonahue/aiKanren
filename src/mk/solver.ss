(library (solver) ; Constraint solving
  (export run-constraint simplify-=/=) ;TODO trim exports
  (import (chezscheme) (state) (negation) (datatypes) (utils) (debugging) (mini-substitution))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (cert (goal? g) (state-or-failure? s)) ; -> state-or-failure?
    (let-values ([(committed pending s) (solve-constraint g s succeed succeed succeed)])
      (store-constraint s pending)))
  
  (org-define (solve-constraint g s conjs committed pending)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (cert (goal? g) (state-or-failure? s) (goal? conjs)) ; -> committed pending state-or-failure?
    (exclusive-cond
     [(fail? g) (values fail fail failure)]
     [(succeed? g) (if (succeed? conjs) (values committed pending s) (solve-constraint conjs s succeed committed pending))]
     [(==? g) (solve-== g s conjs committed pending)]
     [(noto? g) (solve-noto (noto-goal g) s conjs committed pending)]
     [(disj? g) (solve-disj3 g s conjs committed pending)]
     [(conde? g) (solve-constraint (conde->disj g) s conjs committed pending)]
     [(conj? g) (solve-constraint (conj-car g) s (conj (conj-cdr g) conjs) committed pending)]
     [(constraint? g) (solve-constraint (constraint-goal g) s conjs committed pending)]
     [(fresh? g) (let-values ([(g s p) (g s empty-package)])
		   (solve-constraint g s conjs committed pending))]
     [(matcho? g) (solve-matcho g s conjs committed pending)]
     [(pconstraint? g) (solve-pconstraint g s conjs committed pending)]
     [(trace-goal? g) (solve-constraint (trace-goal-goal g) s conjs committed pending)]
     [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)]))

  (define (solve-noto g s ctn committed pending)
    (if (==? g) (solve-=/= g s ctn committed pending)
	(let-values ([(g h s^) (solve-constraint g s succeed committed pending)])
	  (let* ([g (noto g)] ;TODO should solve noto solve the positive goal with ctn and then simply transform the result somehow?
		[h (noto h)]
		[gh (disj g h)])
	    (if (fail? gh) (values fail fail failure) ;TODO scrutinize precisely which goals must be returned and which may solve further
		(solve-constraint ctn (store-constraint s gh) succeed (conj committed gh) pending))))))
  
  (org-define (solve-== g s ctn committed pending)
    ;; Runs a unification, collects constraints that need to be rechecked as a result of unification, and solves those constraints.
    ;;TODO is it possible to use the delta on == as a minisubstitution and totally ignore the full substitution when checking constraints? maybe we only have to start doing walks when we reach the simplification level where vars wont be in lowest terms
    ;;TODO quick replace extended vars in constraints looked up during unify and check for immediate failures
    ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
    ;; TODO can we sort our conjunctions into those containing variables not touched by the current unifications and so may need to be further walked/solved and those that we can just directly strap on to the out parameter now? may have to do with analyzing which ones have disjunctions that are still normalized even after updates with current unifications
    ;;TODO we can construct the unified normalized goal as a binary tree no var ids and make it faster to use it as a mini substitution for further simplification
    (let-values ([(g c s) (unify s (==-lhs g) (==-rhs g))]) ; g is the conjunction of normalized unifications made. c is the conjunction of constraints that need to be rechecked.
      (cert (goal? c))
      (org-display g c)
      (if (or (fail? g) (occurs-check* g s)) (values fail fail failure)
	  (solve-constraint c s ctn (conj committed g) pending))))
#;
  (define (simplify-== g us)
    3)

  (define (occurs-check* g s) ; TODO add a non occurs check =!= or ==!
    ;; TODO can we pack eigen checks onto occurs check and get them for free?
    (cert (or (conj? g) (==? g) (succeed? g)))
    (exclusive-cond
     [(conj? g) (and (occurs-check* (conj-lhs g) s) (occurs-check* (conj-rhs g) s))]
     [(succeed? g) #f]
     [else (occurs-check s (==-lhs g) (==-rhs g))]))

  (define (occurs-check s v term) ;TODO see if the normalized ==s can help speed up occurs-check, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification?
	      (cert (state? s) (var? v))
	      (exclusive-cond
	       [(eq? v term) #t] ; term is already walked by normalized ==s
	       [(pair? term)
		(or (eq? v (car term)) (eq? v (cdr term)) ; can't just walk a term bc it is already in the substitution
		 (occurs-check s v (walk-var s (car term))) (occurs-check s v (walk-var s (cdr term))))]
	       [else #f]))
  
  (org-define (solve-=/= g s ctn committed pending)
	      ;; Solves a =/= constraint lazily by finding the first unsatisfied unification and suspending the rest of the unifications as disjunction with a list =/=.
	      ;;TODO can we just add the =/= disjunction directly to the state and let the solver deal with it? might have to report it as added rather than pending once the two constraint return system is in place
    (cert (==? g)) ; -> goal? state?
    (let-values ([(g c) (disunify s (==-lhs g) (==-rhs g))]) ; g is normalized x=/=y, c is constraints on x&y, s^ is s without c
      (org-display g)
      (if (or (succeed? g) (fail? g)) (solve-constraint g s ctn committed pending) ; If g is trivially satisfied or unsatisfiable, skip the rest and continue with ctn.
	  (let-values ([(unified disunified recheck diseq) (simplify-=/= c (=/=-lhs (disj-car g)) (=/=-rhs (disj-car g)) (disj-car g))]) ; Simplify the constraints with the first disjoined =/=.
	    (if (fail? unified) (solve-constraint ctn s succeed committed pending) ; If the constraints entail =/=, skip the rest and continue with ctn.
		(let-values ([(g0 p0 s0) (solve-constraint recheck (extend s (=/=-lhs (disj-car g)) (conj diseq disunified)) ctn succeed succeed)]) ; Check that the constraints that need to be rechecked are consistent with x=/=y
		  (org-display g0 s0)
		  (cond
		   [(noto? g) (values (conj committed (conj g g0)) pending s0)] ; This is not a disjunction, so just modify the state and proceed with whatever the value. The normal form consists of the =/= conjoined with the normal form of the constraint we had to remove from the state and recheck. Simplified portions of the constraint we added back to s0 are already in s0. s0 already entails ctn, so we are done.
		   [(fail? g0) (solve-constraint (disj-cdr g) s ctn committed pending)] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
		   ;; The normal form of a disj of =/= is head | (body & ctn), representing the suspension of the continuation over the body goals but not the already-run head goal (as in bind in the normal mk search).
		   [else (org-printf "returning =/=-disj") (values committed (conj pending (disj (disj-car g) (conj (disj-cdr g) ctn))) s)])))))))

  (define (simplify-=/= g x y d)
    ;; Simplifies the constraint g given the new constraint x=/=y. Simultaneously constructs 4 goals:
    ;; 1) g simplified under the assumption x==y. If fail?, g => x=/=y, so we can simply throw away the new constraint. Since we only need to check for failure, we can cut corners and not compute the true simplification of g, g', so long as ~g <=> ~g'.
    ;; 2) g simplified under x=/=y but only conjuncts that are completely normalized. Since they are guaranteed to be already normalized, we can simply add them directly to the store.
    ;; 3) g simplified under x=/=y, but only conjuncts that might be unnormalized. We must re-check these with the full solver.
    ;; 4) The final disequality constraint x=/=y. If it is already entailed by our simplifications of g, just return succeed. This will be conjoined to the constraint from #2 when adding to the store.
    (cert (goal? g)) ; -> goal?(unified) goal?(disunified) goal?(recheck) goal?(disequality)
    (exclusive-cond
     [(succeed? g) (values succeed succeed succeed d)] ; If no constraints on x, add succeed back to the store.
     [(fail? g) (values fail fail fail fail)] ; Empty disjunction tail. Fail is thrown away by disj.
     [(==? g) (let* ([s (list (cons (==-lhs g) (==-rhs g)))]
		     [s^ (mini-unify s x y)])
		(cond
		 [(failure? s^) (values fail g succeed d)] ; == different from =/= => =/= satisfied
		 [(eq? s s^) (values g fail succeed d)] ; == same as =/= => =/= unsatisfiable
		 [else (values g g succeed d)]))] ; free vars => =/= undecidable
     [(pconstraint? g) (if (pconstraint-attributed? g x) (values (pconstraint-check g x y) g succeed d) (values g g succeed d))] ; The unified term succeeds or fails with the pconstraint. The disunified term simply preserves the pconstraint.
     [(matcho? g) (if (and (matcho-attributed? g x) (not (or (var? y) (pair? y)))) (values fail g succeed d) ; Check that y could be a pair.
		      (values g g succeed d))] ;TODO add patterns to matcho and check them in simplify-=/= 
     [(noto? g) (let-values ([(unified disunified recheck d) (simplify-=/= (noto-goal g) x y d)]) ; Cannot contain disjunctions so no need to inspect returns.
		  (cert (succeed? recheck)) ; noto only wraps primitive goals, which should never need rechecking on their own
		  (values (noto unified) (noto disunified) recheck d))]
     [(conj? g) (let-values ([(unified disunified-lhs recheck-lhs d) (simplify-=/= (conj-lhs g) x y d)])
		  (if (fail? unified) (values fail disunified-lhs recheck-lhs d) ; If unified fails, we can throw the =/= away, so abort early.
		      (let-values ([(unified disunified-rhs recheck-rhs d) (simplify-=/= (conj-rhs g) x y d)])
			(values unified (conj disunified-lhs disunified-rhs) (conj recheck-lhs recheck-rhs) d))))]
     [(disj? g) (let*-values ([(unified-lhs simplified-lhs recheck-lhs d) (simplify-=/= (disj-car g) x y d)]
			      [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
		  (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d) ; If the whole disjunction succeeds because it contained a single x=/=y, skip the rest of the computation and preserve the final disequality to conjoin to the whole constraint (or subsequent disjunction)
		      (let*-values ([(unified-rhs simplified-rhs recheck-rhs d) (simplify-=/= (disj-car (disj-cdr g)) x y d)]
				    [(disunified-rhs) (conj simplified-rhs recheck-rhs)]) ; We need to check the first two disjuncts for failure and recheck the whole disjunction if either fails.
			(if (succeed? disunified-rhs) (values unified-lhs succeed succeed d)
			    (let*-values ([(unified-tail simplified-tail recheck-tail _) (simplify-=/= (disj-cdr (disj-cdr g)) x y succeed)]
					  [(disunified-tail) (conj simplified-tail recheck-tail)]) ; Tail may not be normalized,, but we can see if it happens to universally fail or succeed as those result in cleaner normal forms.
			      (if (succeed? disunified-tail) (values unified-tail succeed succeed d) ; If the tail succeeds, abort.
			       (let* ([unified (disj unified-lhs (disj unified-rhs unified-tail))] ; If all disjuncts fail, x=/=y is already entoiled by the disjunction as a whole and can be discarded.
				      [disunified (if (or (fail? unified-lhs) (fail? disunified-lhs)) ; Place the disequality as deep into the disjunction as possible provided it is already entailed by all previous disjuncts.
						      (if (or (fail? unified-rhs) (fail? disunified-rhs)) ;TODO push the diseq as far back as needed by giving it to the tail computation if we would otherwise append it before tail
							  (if (or (fail? unified-tail) (equal? unified-tail (== x y)))
							      (disj disunified-lhs (disj disunified-rhs disunified-tail))
							      (disj disunified-lhs (disj disunified-rhs (conj d disunified-tail))))
							  (disj disunified-lhs (conj d (disj disunified-rhs disunified-tail))))
						      (conj d (disj disunified-lhs (disj disunified-rhs disunified-tail))))])
				 (if (or (fail? simplified-lhs) (fail? simplified-rhs) ; Recheck if there was a failure in one of the first two disjuncts,
					 (not (succeed? recheck-lhs)) (not (succeed? recheck-rhs))) ; or if a subgoal disjunct needs to be rechecked.
				     (values unified succeed disunified succeed) ; TODO if disj1 contains no ==, and disj-tail fails, we do not need to recheck disj2
				     (values unified disunified succeed succeed)))))))))]
     [else (assertion-violation 'simplify-=/= "Unrecognized constraint type" g)]))
  
  (define (solve-matcho g s ctn committed pending)
    (if (null? (matcho-out-vars g)) ; Expand matcho immediately if all vars are ground
	(let-values ([(_ g s p) (expand-matcho g s empty-package)])
	  (solve-constraint g s ctn committed pending)) ;TODO replace walkvar in matcho solver with walk once matcho handles walks
	(let ([v (walk-var s (car (matcho-out-vars g)))]) ;TODO this walk should be handled by == when it replaces var with new binding
	  ;;TODO if we get a non pair, we can fail matcho right away without expanding lambda
	  (if (var? v) ; If first out-var is free,
	      (let ([m (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g))]) ; store the matcho. 
		(solve-constraint ctn (store-constraint s m) succeed (conj committed m) pending)) ; Otherwise, keep looking for a free var.
	      ;;TODO just operate on the list for matcho solving
	      (solve-matcho (make-matcho (cdr (matcho-out-vars g)) (cons v (matcho-in-vars g)) (matcho-goal g)) s ctn committed pending)))))

  (define (solve-disj g s ctn committed pending) ;TODO solve-disj should compress disjs with shared == into one disjunct conjoined to the ==
    ;; The solver attempts to find ==s common to all disjuncts and factor them out. If it fails, it puts the failing disjunct at the head (failing because it had no ==s in common with previous disjuncts, either because it had none or it had different ones) and factors any common ==s out of those it has searched and puts them second as one disjunct (properly factored and conjoined to their common ==s). This yields 3 possible normal forms for disjunctions:
    ;; (=/=, unnormalized ...) a head disjunct containing no ==s and the rest unnormalized. This happens if the first non failing disjunct it finds has no ==s
    ;; (=/=, ==&normalized, unnormalized ...) a head disjunct containing no ==s and a "neck" disjunct beneath it that is a conjunction of one or more ==s and an arbitrary normalized constraint. This happens when the search is terminated early by a disjunct with no ==s.
    ;; (==1, ==2&normalized, unnormalized ...) a head disjunct containing some ==s and a "neck" disjunct beneath it that is a conjunction of one or more ==s (all distinct from the ==s in the first disjunct) and an arbitrary normalized constraint. This happens when the search is terminated early by a disjunct with different ==s.
    ;; A normalized disjunction headed by a =/= (goal without ==s) need only be rechecked if the head goal fails, or if a subgoal of the first disjunct is a disjunction that needs to be rechecked, and so need only be attributed to the first disjunct's variables.
    ;; A normalized disjunction headed by a == (goal with ==s) must be rechecked if either the first or second disjuncts fail or contains a disjunction that needs to be rechecked, since either might imply the ability to commit to the ==s in the other.
    ;; TODO can neighboring disjs cancel each other, eg x==1|x=/=1 => succeed
    (let-values ([(head-disj ==s neck-disj g s) (solve-disj* g s ctn fail)]) ; The head disjunct is the first that does not unify vars common to previous disjuncts, or fail if all share at least one ==.
      (org-display head-disj ==s neck-disj g) ; TODO make disj return via committed path if all but one fail
      (values committed (conj pending (disj head-disj (disj (conj ==s neck-disj) g))) s)))
  
  (org-define (solve-disj* g s ctn ==s) ;TODO disj can use solved head disjs to propagate simplifying info to other disjuncts. look for tautologies
    (cert (goal? g) (state? s) (goal? ctn)) ; -> head-disj ==s neck-disj tail-disj state?
    (if (fail? g) (values fail ==s fail fail failure) ; Base case: no more disjuncts to analyze. Failure produced by disj-cdr on a non-disj?.
	(let*-values ([(h0 i0 s0) (solve-constraint (disj-car g) s ctn succeed succeed)]
		      [(g0) (conj h0 i0)]) ; First, solve the head disjunct.
	  (org-exclusive-cond g0-cond
			      [(succeed? g0) (values succeed fail fail succeed s)] ; First disjunct succeeds => entire constraint is already satisfied.
			      [(fail? g0) (solve-disj* (disj-cdr g) s ctn ==s)] ; First disjunct fails => check next disjunct.
			      ;;TODO do we have to continue to check ==s if the returned disj might commit?
			      [(disj? g0) (values (disj-car g0) ==s fail (disj (disj-cdr g0) (conj (disj-cdr g) ctn)) s)] ; First disjunct itself a disjunction => whole disjunction not reducible otherwise that disjunction would have normalized to a non-disjunction.
			      [else
			       (let ([==s (if (fail? ==s) (conj-filter g0 ==?) (conj-intersect ==s g0))]) ; Find ==s in common with previous disjuncts or filter them out of the first disjunct (signified by ==s = fail)
				 (org-if if-==s (succeed? ==s) ; If there are none,
					 (if (disj? g) ; return the disjunct that breaks the pattern to be the new head. We make it the head because when it fails, it is worth reconsidering the disjuncts with common ==s.
					     (values (disj-car g0) ==s fail (disj (disj-cdr g0) (conj (disj-cdr g) ctn)) s) ;TODO does disj account for terminal disj subgoals?
					     (values g0 ==s fail fail s0)) ; The tail should return the modified state in case we can get away with committing to it if all previous disjuncts fail. 
					 (let-values ([(head-disj ==s neck-disj g s^) (solve-disj* (disj-cdr g) s ctn ==s)]) ; Solve the rest of the disjuncts
					   (org-exclusive-cond rest-cond
							       [(and (fail? g) (fail? head-disj) (fail? neck-disj)) (values fail ==s (conj-diff g0 ==s) fail s0)] ; If tail fails, propagate the modified state.
							       [(succeed? g) (values succeed fail fail succeed s)] ; Propagate trivial success up through disjunction.
							       ;; Propagate the new head.
							       [else (org-display g0 ==s neck-disj g) (values head-disj ==s (disj (conj-diff g0 ==s) neck-disj) g s)]))))]))))

  #;
  (define (solve-disj2 g s ctn committed pending) ;TODO can solve-disj be cps?
    (exclusive-cond
     [(disj? g) (let-values ([(a b c) (solve-disj2 (disj-lhs g) s ctn committed pending)])
		  3)]
     [(conj? g) (nyi disj conj)]
  [else (solve-constraint g s ctn committed pending)]))

  (org-define (solve-disj3 g s ctn committed pending) ;TODO can solve-disj be cps?
    (let*-values ([(c-lhs p-lhs s-lhs) (solve-constraint (disj-lhs g) s ctn succeed succeed)]
		  [(lhs) (conj c-lhs p-lhs)])
      (org-display c-lhs p-lhs s-lhs)
      (exclusive-cond
       [(succeed? lhs) (values committed pending s)]
       [(fail? lhs) (solve-constraint (disj-rhs g) s ctn committed pending)]
       [else 
	(let*-values ([(c-rhs p-rhs s-rhs) (solve-constraint (disj-rhs g) s ctn succeed succeed)]
		      
		      [(rhs) (conj c-rhs p-rhs)]
		      [(cs ds lhs rhs) (disj-factorize lhs rhs)])
	  (org-display c-rhs p-rhs s-rhs)
	  (values committed (conj pending (conj cs (conj (disj lhs rhs) ds))) s))])))

  (define solve-pconstraint ; TODO add guard rails for pconstraints returning lowest form and further solving
    (case-lambda ;TODO solve-pconstraint really only needs to be called the first time. after that pconstraints solve themselves
      [(g s ctn committed pending) (solve-pconstraint g s ctn committed pending '())]
      [(g s ctn committed pending vs)
       (if (not (pconstraint? g)) (solve-constraint g s ctn committed pending)
	   (let ([var (find (lambda (v) (not (memq v vs))) (pconstraint-vars g))])
	     (if (not var) (solve-constraint ctn (store-constraint s g) succeed (conj committed g) pending) ; All vars walked. Store constraint.
		 (let-values ([(var^ val) (walk-var-val s var)])
		   (cond
			 [(eq? var val) (solve-pconstraint g s ctn committed pending (cons var^ vs))] ; Ignore free vars. There should be no ground terms in pconstraint vars list.
			 [(goal? val) (solve-pconstraint ((pconstraint-procedure g) var var^ val (pconstraint-data g))
							 s ctn committed pending (cons var^ vs))]
			 [else (solve-pconstraint ((pconstraint-procedure g) var^ val (pconstraint-data g))
						  s ctn committed pending (cons var^ vs))])))))]))

  (define (store-constraint s g) ;TODO make store constraint put disj right and everything else left
    ;; Store simplified constraints into the constraint store.
    (cert (state-or-failure? s) (goal? g) (not (conde? g))) ; -> state?
    (exclusive-cond
     [(fail? g) failure]
     [(succeed? g) s]
     [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
     [(==? g) (extend s (==-lhs g) (==-rhs g))]
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s g (attributed-vars g))]))
  
  (define attributed-vars ;TODO thread trace-goal through other critical infrastructure so its semantically transparent
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (case-lambda ;TODO create a defrel that encodes context information about what vars were available for use in reasoning about which freshes might be able to unify them within their lexical scope
      [(g) (let-values ([(vs unifies) (attributed-vars g '() #f)]) vs)]
      [(g vs unifies)
       (cert (goal? g))
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
	 (cert (var? (==-lhs g)))
	 (values (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs)) #t)]
	[(matcho? g)
	 (values (if (or (null? (matcho-out-vars g)) (memq (car (matcho-out-vars g)) vs)) vs (cons (car (matcho-out-vars g)) vs)) unifies)]
	[(pconstraint? g)
	 (values (fold-left (lambda (vs v) (if (memq v vs) vs (cons v vs))) vs (pconstraint-vars g)) unifies)]
	[(constraint? g) (attributed-vars (constraint-goal g) vs unifies)]
	[else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])])))
