(library (solver) ; Constraint solving
  (export run-constraint simplify-=/=2) ;TODO trim exports
  (import (chezscheme) (state) (negation) (datatypes) (utils) (debugging) (mini-substitution))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (cert (goal? g) (state-or-failure? s)) ; -> state-or-failure?
    (call-with-values (lambda () (solve-constraint g s succeed succeed)) store-disjunctions))
  
  (org-define (solve-constraint g s conjs out)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (cert (goal? g) (state-or-failure? s) (goal? conjs)) ; -> goal? state-or-failure?
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
     [(trace-goal? g) (solve-constraint (trace-goal-goal g) s conjs out)]
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
    ;; TODO can we sort our conjunctions into those containing variables not touched by the current unifications and so may need to be further walked/solved and those that we can just directly strap on to the out parameter now? may have to do with analyzing which ones have disjunctions that are still normalized even after updates with current unifications
    ;;TODO we can construct the unified normalized goal as a binary tree no var ids and make it faster to use it as a mini substitution for further simplification
    (let-values ([(g c s) (unify s (==-lhs g) (==-rhs g))]) ; g is the conjunction of normalized unifications made. c is the conjunction of constraints that need to be rechecked.
      (cert (goal? c))
      (if (or (fail? g) (occurs-check* g s)) (values fail failure)
	  (solve-constraint c s ctn (conj out g)))))

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
  
  (org-define (solve-=/= g s ctn out)
    (cert (==? g))
    (let-values ([(g c s^) (disunify s (==-lhs g) (==-rhs g))]) ; g is normalized x=/=y, c is constraints on x&y, s^ is s without c
      (org-display g)
      (if (or (succeed? g) (fail? g)) (solve-constraint g s ctn out)
	  (let-values ([(aborted? simplified recheck diseq) (simplify-=/= c (==-lhs (noto-goal (disj-car g))) (==-rhs (noto-goal (disj-car g))) (disj-car g))]) ; Evaluate constraints with the first disequality in the store.
	    (org-display aborted? simplified recheck)
	    (if aborted? (solve-constraint aborted? s ctn out)
	     (let-values ([(g0 s0) (solve-constraint recheck (extend s (==-lhs (noto-goal (disj-car g))) (conj simplified diseq)) ctn succeed)])
					;	    (org-display (extend s (==-lhs (noto-goal (disj-car g))) simplified) (store-constraint s^ simplified))
	       (org-display g0 s0)
	       (if (noto? g) (values (conj out (conj g g0)) s0) ; This is not a disjunction, so just modify the state and proceed with whatever the value. 
		   (org-exclusive-cond first-disj-=/=
				       ;[(succeed? g0) (values (conj g out) s^)] ; The constraints on the attributed vars are trivial, so simply return the entire disjunction and the unmodified state.
				       ;;TODO let solve constraint handle fail case
				       [(fail? g0) (solve-constraint (disj-cdr g) s ctn out)] ; The head of the disjunction fails, so continue with other disjuncts unless we are out, in which case fail.
				       ;; To suspend a disjunction, conjoin the output var, the head of the disjunction that has already been simplified, and a disjunction of the constraints on the head attributed vars with the continuation bound to the tail of the disjunction.
				       ;; TODO potential opportunity to store the whole disjunction instead of just the head and reuse the state if =/= is the top level disjunction
				       [else (org-printf "returning =/=-disj") (values (conj out (conj (disj (disj-car g) (conj (disj-cdr g) ctn)) g0)) (if (succeed? recheck) s (unbind-constraint s (==-lhs (noto-goal (disj-car g))))))]))))))))


  ;; encountering a goal that makes =/= trivial in conj should fail early
  ;; if all disjs make a =/= trivial also fail early
  ;; if no disjs, conjoin to end
  ;; if disjs, conjoin as far inside first as needed but simplify everything
  ;; if first disj fails, and second has ==, rerun
  ;; double succeed implies trivial, dont modify subst
  ;; if a doesnt drivialize and still has constraint in recursion, do rest with succeed and conjoin at that point
  ;; disj may start either with no ==, or == not shared by 2nd disj
  ;; disj 1: (=/=, unwalked ...)
  ;; disj 2: (==1, ==2, unwalked ...)
  ;; disj 3: (=/=, ==1, unwalked ...)
  ;; for disj:
  ;; simplify first disjunct
  ;; if fail, we need to rewalk the constraint
  ;; if abort, keep and continue
  ;; if constraints compatible, if first not had ==s, just wrap the rest and contniue
  ;; if compatible and first had ==s, see if we can make the second fail
  ;; if first has failing ==, the second was at least normalized but cant fail. if it succeeds, we succeed 
  ;; (symbolo x) => x=/=3 is always true
  ;; x=/=3 <=> x=/=3 is always true (replace with identical term, eg skip modification)
  ;; (symbolo x) | (symbolo x) => x=/=3 is always true
  ;; (symbolo x) | x=/=3 <=> x=/=3 is always true (replace with simpler term eg x=/=3)
  ;; (symbolo x) => simplified ~simplifies
  ;; (numbero x) => ~simplified ~simplifies
  ;; x=/=3 => simplified simplifies
  ;; x==3 => fail fail
  ;; only disjunctions get replaced, so only need to overwrite constraint if there are disjunctions or we dont throw away the =/=
  ;;
  ;; 1: throw away the new constraint without modification, 2: modify the current constraint and continue, 3: modify the constraint and recheck something. failure is never an option
  ;; (not (numbero x)) => simplified ~simplifies
  ;; (symbolo x) = fail => succeed (symbolo x) ; fail
  ;; (numbero x) = succeed => x=/=3 (numbero x)
  ;; (not (symbolo x)=fail)=succeed => x=/=3 (not (symbolo x))
  ;; (not (numbero x)=succeed)=fail => succeed (not (numbero x))
  ;; x==3=fail => fail fail
  ;; x=/=3=succeed => succeed
  ;; not matcho=fail => x=/=3 matcho
  ;;
  ;; calculate what happens to the constraint under unification. if it fails, the =/= is irrelevant. or if it succeeds under negation
  (define (simplify-=/=2 g x y)
    (exclusive-cond
     [(succeed? g) (values succeed succeed succeed)] ; If no constraints
     [(==? g) (let* ([s (list (cons (==-lhs g) (==-rhs g)))]
		     [s^ (mini-unify s x y)])
		(cond
		 [(failure? s^) (values fail fail fail)] ; == different from =/= => =/= satisfied
		 [(eq? s s^) (values succeed succeed fail)] ; == same as =/= => =/= unsatisfiable
		 [else (values g g succeed)]))] ; free vars => =/= undecidable
     [(pconstraint? g) (if (pconstraint-attributed? g x) (values (pconstraint-check g x y) g succeed) (values g g succeed))]
     [(matcho? g) (if (and (matcho-attributed? g x) (not (or (var? y) (pair? y)))) (values fail fail fail)
		      (values g g succeed))]
     [(noto? g) (let-values ([(h _ _2) (simplify-=/=2 (noto-goal g) x y)]) ; Cannot contain disjunctions so no need to inspect returns.
		  (values (noto h) g succeed))]
     [(conj? g) (let-values ([(entailed simplified-lhs recheck-lhs) (simplify-=/=2 (conj-lhs g) x y)])
		  (if (fail? entailed) (values fail simplified-lhs recheck-lhs)
		      (let-values ([(entailed simplified-rhs recheck-rhs) (simplify-=/=2 (conj-rhs g) x y)])
			(org-display  simplified-lhs simplified-rhs recheck-lhs recheck-rhs)
			(values entailed (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
     ;; if the first param is fail, =/= already entailed there: something already fails when it will. if second param true, its bidirectional so replace whole disj, otherwise check next one
     [(disj? g) (let-values ([(entailed-lhs simplified-lhs recheck-lhs) (simplify-=/=2 (disj-car g) x y)]
			     [(entailed-rhs simplified-rhs recheck-rhs) (simplify-=/=2 (disj-car (disj-cdr g)) x y)])
		  
		  (if (fail? entailed-lhs)
		      (if (fail? entailed-rhs)
			  (let ([ctn (conj (=/= x y) (disj-cdr (disj-cdr g)))])
			    (values ctn (disj simplified-lhs (disj simplified-rhs ctn)) succeed))
			  (nyi rhs not entailed))
		      (nyi lhs not entailed))
		  )
      
      ]))

  #;
  (if (eq? x (==-lhs g))
		  (if (eq? y (==-rhs g))
		      (values succeed)
		      (if (or (var? y) (var? (==-rhs g))) (values g) (values fail)))
		  (if (or (var? x) (var? (==-lhs g)))
		      (if (and (not (var? y)) (not (var? (==-rhs g))) (not (eq? y (==-rhs g)))) (values fail) (values g))))
  
  (org-define (simplify-=/= g x y xy)
    (org-exclusive-cond simplify-cond
     [(succeed? g) (values #f succeed succeed xy)]
     [(conj? g) (let-values ([(abort? simplified-lhs recheck-lhs xy) (simplify-=/= (conj-lhs g) x y xy)])
		  (if abort? (values abort? simplified-lhs recheck-lhs xy)
		      (let-values ([(abort? simplified-rhs recheck-rhs xy) (simplify-=/= (conj-rhs g) x y xy)])
			(values abort? (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs) xy))))]
     [(noto? g)
      (exclusive-cond
       [(==? (noto-goal g))
	(if (and (eq? y (==-rhs (noto-goal g))) (eq? x (==-lhs (noto-goal g))))
	    (values succeed succeed succeed xy)
	    (values #f g succeed xy))]
       [(pconstraint? (noto-goal g))
	(if (succeed? (pconstraint-check (noto-goal g) x y)) ; A pconstraint that always fails when == obsoletes the =/=.
	    (values succeed succeed succeed xy)
	    (values #f g succeed xy))]
       [else (values #f g succeed xy)])]
     [(disj? g) (let-values ([(abort? simplified recheck xy) (simplify-=/= (disj-car g) x y xy)])
		  (org-display abort? simplified recheck)
		  (org-exclusive-cond =/=-disj-simplify
		   [(fail? abort?)
		    (let-values ([(abort? simplified recheck xy) (simplify-=/= (disj-car (disj-cdr g)) x y xy)])
		      (values #f succeed (conj simplified recheck) xy))]
		   [(succeed? abort?)
		    (let-values ([(abort? simplified recheck xy) (simplify-=/= (disj-cdr g) x y xy)])
		      (values #f succeed (conj simplified recheck) xy))]
		   [else (values #f succeed g xy)]))]
     [(matcho? g) (if (not (or (var? y) (pair? y))) (values succeed succeed succeed xy)
		      (values #f g succeed xy))] ;TODO =/= can simplify more precisely against matcho if it uses the actual pattern and not just pair?
     [(==? g) (if (and (eq? y (==-rhs g)) (eq? x (==-lhs g)))
		  (values fail fail fail xy)
		  (values #f g succeed xy))]
     [(pconstraint? g) (if (fail? (pconstraint-check g x y))
			   (values succeed succeed succeed xy)
			   (values #f g succeed xy))]
     [else (assertion-violation 'simplify-=/= "Unrecognized constraint type" g)]))

  ;; a =/= anywhere should discard the whole disjunction, but not abort early
  ;; a symbolo means the =/= isnt needed in that disjunct, continue searching
  ;; a == that conflicts fails, toss the disjunct
  (org-define (simplify-=/=-disj g x y)
	      (exclusive-cond
	       [(==? g) (if (and (eq? y (==-rhs g)) (eq? x (==-lhs g))) fail g)]
	       [(disj? g) (disj (simplify-=/=-disj (disj-car g) x y) (simplify-=/=-disj (disj-cdr g) x y))]
	       [else (assertion-violation 'simplify-=/=-disj "Unrecognized constraint type" g)]))
  
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

  (define (solve-disj g s ctn out) ;TODO solve-disj should compress disjs with shared == into one disjunct conjoined to the ==
    ;; The solver attempts to find ==s common to all disjuncts and factor them out. If it fails, it puts the failing disjunct at the head (failing because it had no ==s in common with previous disjuncts, either because it had none or it had different ones) and factors any common ==s out of those it has searched and puts them second as one disjunct (properly factored and conjoined to their common ==s). This yields 3 possible normal forms for disjunctions:
    ;; (=/=, unnormalized ...) a head disjunct containing no ==s and the rest unnormalized. This happens if the first non failing disjunct it finds has no ==s
    ;; (=/=, ==&normalized, unnormalized ...) a head disjunct containing no ==s and a "neck" disjunct beneath it that is a conjunction of one or more ==s and an arbitrary normalized constraint. This happens when the search is terminated early by a disjunct with no ==s.
    ;; (==1, ==2&normalized, unnormalized ...) a head disjunct containing some ==s and a "neck" disjunct beneath it that is a conjunction of one or more ==s (all distinct from the ==s in the first disjunct) and an arbitrary normalized constraint. This happens when the search is terminated early by a disjunct with different ==s.
    ;; A normalized disjunction headed by a =/= (goal without ==s) need only be rechecked if the head goal fails, and so need only be attributed to the first disjunct's variables.
    ;; A normalized disjunction headed by a == (goal with ==s) must be rechecked if either the first or second disjuncts fail, since either might imply the ability to commit to the ==s in the other.
    (let-values ([(head-disj ==s neck-disj g s) (solve-disj* g s ctn fail fail)]) ; The head disjunct is the first that does not unify vars common to previous disjuncts, or fail if all share at least one ==.
      (cert (goal? head-disj))
      (org-display head-disj ==s neck-disj g)
      (values (conj out (disj head-disj (disj (conj ==s neck-disj) g))) (if (and (fail? head-disj) (not (or (succeed? ==s) (fail? ==s)))) (store-== s ==s) s))))
  
  (org-define (solve-disj* g s ctn ==s parent-disj)
    (cert (goal? g) (state? s) (goal? ctn)) ;TODO disj can use solved head disjs to propagate simplifying info to other disjuncts
    (exclusive-cond
     [(fail? g) (values fail ==s fail fail failure)] ; Base case: no more disjuncts to analyze. Failure produced by disj-cdr on a non-disj?.
     [else (let-values ([(g0 s0) (solve-constraint (disj-car g) s ctn succeed)]) ; First, solve the head disjunct.
	     (org-exclusive-cond g0-cond
	      [(succeed? g0) (values succeed fail fail succeed s)] ; First disjunct succeeds => entire constraint is already satisfied.
	      [(fail? g0) (solve-disj* (disj-cdr g) s ctn ==s parent-disj)] ; First disjunct fails => check next disjunct.
	      ;;TODO do we have to continue to check ==s if the returned disj might commit?
	      [(disj? g0) (values (disj-car g0) ==s fail (disj (disj-cdr g0) (conj (disj-cdr g) ctn)) s)] ; First disjunct itself a disjunction => whole disjunction not reducible otherwise that disjunction would have normalized to a non-disjunction.
	      [else
	       (let ([==s (if (fail? ==s) (conj-filter g0 ==?) (conj-intersect ==s g0))]) ; Find ==s in common with previous disjuncts or filter them out of the first disjunct (signified by ==s = fail)
		 (org-if if-==s (succeed? ==s) ; If there are none,
		     (if (disj? g) ; return the disjunct that breaks the pattern to be the new head. We make it the head because when it fails, it is worth reconsidering the disjuncts with common ==s.
			 (values (disj-car g0) ==s fail (disj (disj-cdr g0) (conj (disj-cdr g) ctn)) s)
			 (values g0 ==s fail fail s0)) ; The tail should return the modified state in case we can get away with committing to it if all previous disjuncts fail. 
		  (let-values ([(head-disj ==s neck-disj g s^) (solve-disj* (disj-cdr g) s ctn ==s g0)]) ; Solve the rest of the disjuncts
		    (org-exclusive-cond rest-cond
		     [(and (fail? g) (fail? head-disj) (fail? neck-disj)) (values fail ==s (conj-diff g0 ==s) fail s0)] ; If tail fails, propagate the modified state.
		     [(succeed? g) (values succeed fail fail succeed s)] ; Propagate trivial success up through disjunction.
		     ;; Propagate the new head.
		     [else (org-display g0 ==s neck-disj g) (values head-disj ==s (disj (conj-diff g0 ==s) neck-disj) g s)]))))]))]))
  
  (define (solve-guardo g s conjs out) ;TODO remove guardo
    (let ([v (walk s (guardo-var g))])
      (exclusive-cond
       [(var? v) (let ([g (guardo v (guardo-procedure g))])
		   (values g (store-constraint s g)))]
       [(pair? v) (solve-constraint ((guardo-procedure g) (car v) (cdr v)) s conjs out)]
       [else (values fail failure)])))


  (define solve-pconstraint ; TODO add guard rails for pconstraints returning lowest form and further solving
    (case-lambda ;TODO solve-pconstraint really only needs to be called the first time. after that pconstraints solve themselves
      [(g s ctn out) (solve-pconstraint g s ctn out '())]
      [(g s ctn out vs)
       (if (not (pconstraint? g)) (solve-constraint g s ctn out)
	   (let ([var (find (lambda (v) (not (memq v vs))) (pconstraint-vars g))])
	     (if (not var) (solve-constraint ctn (store-constraint s g) succeed (conj out g)) ; All vars walked. Store constraint.
		 (let-values ([(var^ val) (walk-var-val s var)])
		   (cond
			 [(eq? var val) (solve-pconstraint g s ctn out (cons var^ vs))] ; Ignore free vars. There should be no ground terms in pconstraint vars list.
			 [(goal? val) (solve-pconstraint ((pconstraint-procedure g) var var^ val (pconstraint-data g))
							 s ctn out (cons var^ vs))]
			 [else (solve-pconstraint ((pconstraint-procedure g) var^ val (pconstraint-data g))
						  s ctn out (cons var^ vs))])))))]))
  
#;
  (define (solve-pconstraint g s ctn out) ; TODO add guard rails for pconstraints returning lowest form and further solving
    (cert (pconstraint? g))
    (let ([g (fold-pconstraint (lambda (g v)
			  (if (pconstraint? g)
			      (let-values ([(v walked) (walk-var-val s v)])
				(if (eq? v walked) g ((pconstraint-procedure g) v walked (pconstraint-data g)))) g))
		      g (pconstraint-vars g))])
      (solve-constraint ctn (store-constraint s g) succeed (conj out g))))
#;
  (define (fold-pconstraint p g vs)
    (if (and (not (null? vs)) (pconstraint? g))
	(fold-pconstraint p (p g (car vs)) (cdr vs))
	g))

  (define (store-== s ==s) ;TODO == should be propagated up and stored at top level, not after every disj. we should propagate one commited conj and one uncommited conj
    (if (conj? ==s) (store-== (store-== s (conj-lhs ==s)) (conj-rhs ==s))
	(begin
	  (cert (==? ==s))
	  (extend s (==-lhs ==s) (==-rhs ==s)))))
  
  (define (store-disjunctions g s)
    (cert (goal? g) (or (fail? g) (not (failure? s))))
    ;; Because solve-constraint has already stored all simple conjoined constraints in the state, throw them away and only put disjunctions in the store.
    (exclusive-cond
     [(conj? g) (store-disjunctions (conj-cdr g) (store-disjunctions (conj-car g) s))]
     [(disj? g) (store-constraint s g)]
     [else s]))

  (define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (cert (state? s) (goal? g) (not (conde? g))) ; -> state?
    (exclusive-cond
     [(succeed? g) s]
     [(fail? g) failure]
     [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s g (attributed-vars g))]))

  (define (invert-disj ds) ds) ;TODO reevaluate inverting disj to put disjuncts with relevant vars at the head to be rechecked
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
	[(guardo? g) (values (if (memq (guardo-var g) vs) vs (cons (guardo-var g) vs)) unifies)]
	[(constraint? g) (attributed-vars (constraint-goal g) vs unifies)]
	[else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])])))
