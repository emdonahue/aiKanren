(library (solver) ; Constraint solving
  (export run-constraint simplify-=/= simplify-pconstraint)
  (import (chezscheme) (state) (negation) (datatypes) (utils) (debugging) (mini-substitution))

  (org-define (run-constraint g s)
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
     [(disj? g) (solve-disj g s conjs committed pending)]
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
    ;;TODO test whether repeated variable transfers inside a disj crowd up the pending constraint
    (let-values ([(bindings simplified recheck s) (unify s (==-lhs g) (==-rhs g))]) ; bindings is a mini-substitution of normalized ==s added to s. c is the conjunction of constraints that need to be simplified or rechecked.
      (cert (goal? simplified) (goal? recheck))
      (cond
       [(fail? bindings) (values fail fail failure)]
       ;; TODO we only need to resimplify if bindings contains a free-free pair (otherwise all individual simplifications are already complete
       [(or (null? bindings) (null? (cdr bindings))) (occurs-check bindings simplified recheck s ctn committed pending)] ; If there is only one binding, it was simplified during unification. We only need to re-simplify if multiple bindings may influence one another.
       [else
	(let-values ([(simplified/simplified simplified/recheck) (simplify-unification simplified bindings)])
	  (if (or (fail? simplified/simplified) (fail? simplified/recheck)) (values fail fail failure)
	      (let-values ([(recheck/simplified recheck/recheck) (simplify-unification recheck bindings)])
		(if (or (fail? recheck/simplified) (fail? recheck/recheck)) (values fail fail failure)
		    (occurs-check bindings simplified/simplified
				  (conj simplified/recheck (conj recheck/simplified recheck/recheck))
				  s ctn committed pending)))))])))

  (define (occurs-check bindings simplified recheck s ctn committed pending)
    (if (not (for-all (lambda (b) (not (occurs-check/binding s (car b) (cdr b)))) bindings)) (values fail fail failure)
	(solve-constraint
	 recheck (store-constraint s simplified) ctn (conj committed (fold-left (lambda (c e) (conj c (make-== (car e) (cdr e)))) succeed bindings)) pending)))

  (define (occurs-check/binding s v term) ;TODO see if the normalized ==s can help speed up occurs-check/binding, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification?
    ;; TODO try implementing occurs check in the constraint system and eliminating checks in the wrong id direction (eg only check lower->higher)
    ;; TODO add a non occurs check =!= or ==!
    ;; Returns #t if it detects a cyclic unification.
    (cert (state? s) (var? v))
    (exclusive-cond
     [(eq? v term) #t] ; term is already walked by normalized ==s
     [(pair? term)
      (or (eq? v (car term)) (eq? v (cdr term)) ; can't just walk a term bc it is already in the substitution
	  (occurs-check/binding s v (walk-var s (car term))) (occurs-check/binding s v (walk-var s (cdr term))))]
     [else #f]))

  (org-define (solve-=/= g s ctn committed pending)
	      ;; Solves a =/= constraint lazily by finding the first unsatisfied unification and suspending the rest of the unifications as disjunction with a list =/=.
	      ;;TODO can we just add the =/= disjunction directly to the state and let the solver deal with it? might have to report it as added rather than pending once the two constraint return system is in place
    (cert (==? g)) ; -> goal? state?
    (let-values ([(g c) (disunify s (==-lhs g) (==-rhs g))]) ; g is normalized x=/=y, c is constraints on x&y
      (if (or (succeed? g) (fail? g)) (solve-constraint g s ctn committed pending) ; If g is trivially satisfied or unsatisfiable, skip the rest and continue with ctn.
	  (if (disj? g) (solve-constraint g s ctn committed pending) ; TODO add flag to let solve-disj know that its constraint might be normalized and to skip initial solving
	   (let-values ([(unified disunified recheck diseq) (simplify-=/= c (=/=-lhs (disj-car g)) (=/=-rhs (disj-car g)) (disj-car g))]) ; Simplify the constraints with the first disjoined =/=.
	     (if (fail? unified) (solve-constraint ctn s succeed committed pending) ; If the constraints entail =/=, skip the rest and continue with ctn.
		 (solve-constraint recheck (extend s (=/=-lhs g) (conj diseq disunified)) ctn (conj committed g) pending)))))))

  (org-define (simplify-=/= g x y d)
    ;; Simplifies the constraint g given the new constraint x=/=y. Simultaneously constructs 4 goals:
    ;; 1) g simplified under the assumption x==y. If fail?, g => x=/=y, so we can simply throw away the new constraint. Since we only need to check for failure, we can cut corners and not compute the true simplification of g, g', so long as ~g <=> ~g'.
    ;; 2) g simplified under x=/=y but only conjuncts that are completely normalized. Since they are guaranteed to be already normalized, we can simply add them directly to the store.
    ;; 3) g simplified under x=/=y, but only conjuncts that might be unnormalized. We must re-check these with the full solver.
    ;; 4) The final disequality constraint x=/=y. If it is already entailed by our simplifications of g, just return succeed. This will be conjoined to the constraint from #2 when adding to the store.
    (cert (goal? g)) ; -> goal?(unified) goal?(disunified) goal?(recheck) goal?(disequality)
x    (exclusive-cond
     [(succeed? g) (values succeed succeed succeed d)] ; If no constraints on x, add succeed back to the store.
     [(==? g) (let* ([s (if (eq? (==-lhs g) x) '() (list (cons (==-lhs g) (==-rhs g))))]
		     [s^ (if (eq? (==-lhs g) x) (mini-unify '() (==-rhs g) y) (mini-unify s x y))]) ;TODO is mini-unify necessary in solve-disj since the constraints should be normalized so we don't have two pairs?
		(exclusive-cond ; unification necessary in case of free vars that might be unified but are not equal, such as (<1> . <2>) == (<2> . <1>)
		 [(failure? s^) (values fail g succeed d)] ; == different from =/= => =/= satisfied
		 [(eq? s s^) (values succeed fail succeed d)] ; == same as =/= => =/= unsatisfiable
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
     [(disj? g) (simplify-=/=-disj g x y d)]
     [(fail? g) (values fail fail fail fail)] ; Empty disjunction tail. Fail is thrown away by disj.
     [(constraint? g) (simplify-=/= (constraint-goal g) x y d)]
     [(procedure? g) (nyi simplify-=/= proceedure)]
     [else (assertion-violation 'simplify-=/= "Unrecognized constraint type" g)]))

  (define (simplify-=/=-disj g x y d)
    (let*-values ([(unified-lhs simplified-lhs recheck-lhs d)
		   (simplify-=/= (disj-lhs g) x y d)]
		  [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
      (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d)
	  (let*-values ([(unified-rhs simplified-rhs recheck-rhs d)
			 (simplify-=/= (disj-rhs g) x y d)]
			[(disunified-rhs) (conj simplified-rhs recheck-rhs)])
	    (if (succeed? disunified-rhs) (values unified-rhs succeed succeed d)
		(let ([unified (disj unified-lhs unified-rhs)])
		  (let-values ([(conjs disjs lhs rhs) (disj-factorize disunified-lhs disunified-rhs)])
		    (let ([disunified
			   (conj conjs (conj
					(if (not (or (fail? unified-lhs) (fail? unified-rhs)))
					    (conj d (disj lhs rhs))
					    (disj (if (fail? unified-lhs) lhs (conj d lhs))
					       (if (fail? unified-rhs) rhs (conj d rhs)))) disjs))])
		      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
			      (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
				   (conj-memp simplified-lhs ==?)))
			  (values unified succeed disunified succeed)
			  (values unified disunified succeed succeed))))))))))

  (org-define (solve-matcho g s ctn committed pending)
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

  (org-define (solve-disj g s ctn committed pending) ;TODO split g in solve-disj into normalized and unnormalized args to let other fns flexibly avoid double solving already normalized constraints
    (let-values ([(c-lhs p-lhs s-lhs) (solve-constraint (disj-lhs g) s ctn succeed succeed)])
      (let* ([lhs (conj c-lhs p-lhs)])
	(if (fail? lhs) (solve-constraint (disj-rhs g) s ctn committed pending)
	    (let*-values ([(c-rhs p-rhs s-rhs)
			   (if (or (not (lazy-solver)) (conj-memp lhs ==?)) (solve-constraint (disj-rhs g) s ctn succeed succeed) ;TODO deal with non left branching disjs that may be created dynamically by =/= or matcho. fundamentally we have to thread information from the first disj through to others and treat them linearly
			       (values succeed (conj (disj-rhs g) ctn) s))]
			  [(rhs) (conj c-rhs p-rhs)])
	      (if (fail? rhs) (values (conj committed c-lhs) (conj pending p-lhs) s-lhs)
		  (values committed (conj pending (disj-factorized lhs rhs)) s)))))))

  (define solve-pconstraint
    (org-case-lambda solve-pconstraint
      [(g s ctn committed pending) (solve-pconstraint g s ctn committed pending '())]
      [(g s ctn committed pending vs) ;-> goal? state?
       (org-if (not (pconstraint? g)) (solve-constraint g s ctn committed pending)
	   (let ([var (find (lambda (v) (not (memq v vs))) (pconstraint-vars g))])
	     (org-if (not var) (solve-constraint ctn (store-constraint s g) succeed (conj committed g) pending) ; All vars walked. Store constraint.
		 (let-values ([(var^ val) (walk-var-val s var)])
		   (org-cond
			 [(eq? var val) (solve-pconstraint g s ctn committed pending (cons var^ vs))] ; Ignore free vars. There should be no ground terms in pconstraint vars list.
			 [(goal? val) (let-values ([(g simplified recheck p)
						    (simplify-pconstraint
						     val ((pconstraint-procedure g) var var^ (pconstraint-data g)))])
					(if (or (fail? g) (fail? simplified) (fail? recheck))
					    (values fail failure)
					 (solve-pconstraint p (extend s var^ simplified) ;TODO can we just stash the pconstraint with the simplified under certain conditions if we know it wont need further solving?
							    (conj recheck ctn) committed pending (cons var^ vs))))]
			 [else (solve-pconstraint ((pconstraint-procedure g) var^ val (pconstraint-data g))
						  s ctn committed pending (cons var^ vs))])))))]))

  (define simplify-pconstraint
    (org-case-lambda simplify-pconstraint
      [(g p) (simplify-pconstraint g p p)]
      [(g p c)
       (cert (or (pconstraint? p) (succeed? p)) (goal? g))
       (cond
	[(succeed? p) (values succeed succeed succeed c)]
	[(conj? g) (let-values ([(p-lhs simplified-lhs recheck-lhs c) (simplify-pconstraint (conj-lhs g) p c)])
		     (if (or (fail? p-lhs) (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail fail fail)
			 (let-values ([(p-rhs simplified-rhs recheck-rhs c) (simplify-pconstraint (conj-rhs g) p c)])
			   (values (if (or (succeed? p-lhs) (succeed? p-rhs)) succeed p) (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs) c))))]
	[(disj? g) (simplify-pconstraint-disj g p c)]
	[(pconstraint? g) (if (equal? p g) (values succeed succeed succeed c)
			      (if (memp (lambda (v) (memq v (pconstraint-vars g))) (pconstraint-vars p))
				  (let-values ([(g simplified recheck) ((pconstraint-procedure g) g p)])
				    (values g simplified recheck c))
				  (values p g succeed c)))]
	[(==? g) (if (memq (==-lhs g) (pconstraint-vars p))
		     (let ([entailed ((pconstraint-procedure p) (==-lhs g) (==-rhs g) (pconstraint-data p))])
		       (values entailed (if (fail? entailed) fail g) succeed c))
		     (values p g succeed c))
	 #;
	 (let-values ([(simplified recheck) (simplify-unification p (->mini-substitution g))])
	 (values simplified g recheck c))]
	;; numbero & not numbero -> succeed succeed -> fail fail
	;; numbero & not symbolo  -> fail fail -> numbero succeed
	;; numbero & =/=1 -> succeed ==1 -> numbero =/=1
	;; numbero & =/='symbol -> fail fail -> numbero succeed
	;; numbero & not symbolo x2 -> numbero symbolo x2 -> numbero not symbolo x2
	[(noto? g) (let-values ([(entailed simplified recheck c) (simplify-pconstraint (noto-goal g) p c)])
		     (org-display entailed simplified recheck)
		     (cert (succeed? recheck))
		     (let ([p (if (and (succeed? entailed) (succeed? simplified)) fail p)])
		       (values p (noto simplified) succeed c)))]
	[else (values p g succeed c)])]))

  (define (simplify-pconstraint-disj g p d)
    (let*-values ([(unified-lhs simplified-lhs recheck-lhs d)
		   (simplify-pconstraint (disj-lhs g) p d)]
		  [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
      (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d)
	  (let*-values ([(unified-rhs simplified-rhs recheck-rhs d)
			 (simplify-pconstraint (disj-rhs g) p d)]
			[(disunified-rhs) (conj simplified-rhs recheck-rhs)])
	    (if (succeed? disunified-rhs) (values unified-rhs succeed succeed d)
		(let ([unified (disj unified-lhs unified-rhs)])
		  (let-values ([(conjs disjs lhs rhs) (disj-factorize disunified-lhs disunified-rhs)])
		    (let ([disunified
			   (conj conjs (conj
					(if (not (or (fail? unified-lhs) (fail? unified-rhs)))
					    (conj d (disj lhs rhs))
					    (disj (if (fail? unified-lhs) lhs (conj d lhs))
						  (if (fail? unified-rhs) rhs (conj d rhs)))) disjs))])
		      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
			      (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
				   (conj-memp simplified-lhs ==?)))
			  (values unified succeed disunified succeed)
			  (values unified disunified succeed succeed))))))))))

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
