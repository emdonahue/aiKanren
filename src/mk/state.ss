(library (state) ; Main state object that holds substitution & constraints
  (export reify reify-var instantiate-var walk state-add-constraint get-constraints remove-constraints unify disunify walk-var walk-var-val extend unbind-constraint simplify-unification) ;;TODO double check state exports. remove extend at least
  (import (chezscheme) (store) (sbral) (datatypes) (negation) (utils) (mini-substitution))

  (define unbound succeed) ; Internal placeholder for unbound variables in the substitution.
  (define unbound? succeed?) ;TODO replace unbound with success as null element in state

  ;; === VARIABLES ===
  
  (define reify ;TODO reify vars inside constraints
    (case-lambda
      [(s v) (reify s v '())]
      [(s v vs) 
       (cond
	[(pair? v) (cons (reify s (car v) vs) (reify s (cdr v) vs))]
	[(var? v)
	 (if (memq v vs) v
	     (let* ([w (walk s v)]
		    [w (if (proxy-constraint? w) (proxy-constraint-constraint w) w)])
	    (if (var? w) w (reify s w (cons v vs)))))]
	[else v])]))

  (define reify-var
    (case-lambda
      [(s v) (reify-var s v '())]
      [(s v vs) 
       (cond
	[(pair? v) (cons (reify-var s (car v) vs) (reify-var s (cdr v) vs))]
	[(var? v)
	 (if (memq v vs) v
	  (let ([w (walk-var s v)])
	    (if (var? w) w (reify-var s w (cons v vs)))))]
	[else v])]))

  (define (walk s v)
    (cert (state? s))
    (let-values ([(binding v) (walk-var-val s v)]) v))

  (define (walk-var s v)
    (let-values ([(binding v) (walk-var-val s v)]) (if (goal? v) binding v)))

  (define (walk-var-val s v)
    (walk-binding (state-substitution s) v))

  (define (substitution-ref s v)
    ;; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
    (cert (sbral? s) (var? v))
    (sbral-ref s (fx- (sbral-length s) (var-id v)) unbound))
  
  (define (walk-binding s v)
    (cert (sbral? s) (not (and (var? v) (zero? (var-id v)))))
    (if (var? v)
	(let ([walked (substitution-ref s v)])
	  (exclusive-cond
	   [(unbound? walked) (values v v)]
	   [(var? walked) (walk-binding s walked)]
	   [else (values v walked)]))
	(values v v)))

  ;; === UNIFICATION ===
  
  (define unify ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system. The substitution also contains constraints on the variable, which must be dealt with by the unifier.
    (org-case-lambda unify
      [(s x y) (unify s x y '())]
      [(s x y bindings)
       (cert (state? s)) ; -> bindings simplified recheck state
       (let-values ([(x-var x) (walk-var-val s x)]
		    [(y-var y) (walk-var-val s y)])
	 (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
	     (unify-binding s y-var y x-var x bindings)
	     (unify-binding s x-var x y-var y bindings)))]))

  (org-define (unify-binding s x-var x y-var y bindings) ; If both vars, x-var guaranteed to have lower id
    (cert (not (or (goal? x-var) (goal? y-var))))
    (cond
       [(goal? x) ; TODO When should simplifying a constraint commit more ==?
	(if (goal? y) (if (eq? x-var y-var) (values bindings succeed succeed s) (extend-constraint s x-var y-var x y bindings)) ; x->y, y->y, ^cx(y)&cy
	    (extend-constraint s x-var y x succeed bindings))] ; x->y, ^cx(y). y always replaces x if x var, no matter whether y var or const
       [(eq? x y) (values bindings succeed succeed s)]
       [(goal? y) (if (var? x)
		      (extend-constraint s x y-var succeed y bindings) ; x->y, y->y, ^cy. y always replaces x due to id, 
		      (extend-constraint s y-var x y succeed bindings))] ; y->x, ^cy(x). unless x is a constant.
       [(var? x) (extend-var s x y bindings)]
       [(var? y) (extend-var s y x bindings)]
       [(and (pair? x) (pair? y)) ;TODO test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify
	(let-values
	    ([(bindings simplified recheck s) (unify s (car x) (car y) bindings)])
	  (if (fail? bindings)
	      (values fail fail fail failure)
	      (let-values ([(bindings simplified^ recheck^ s) (unify s (cdr x) (cdr y) bindings)])
		(values bindings (conj simplified simplified^) (conj recheck recheck^) s))))] ;TODO unify should simplify constraints together as it conjoins them, or perhaps in solve-== after they have all been normalized
       [else (values fail fail fail failure)]))
  
  (define (extend-var s x y bindings)
    ;; Insert a new binding between x and y into the substitution.
    (values (cons (cons x y) bindings) succeed succeed (extend s x y)))

  (org-define (extend-constraint s var val var-c val-c bindings)
    ;; Opportunistically simplifies the retrieved constraints using the available vars and vals and then extends the substitution. If there is a constraint on val (and it is a var), we must explicitly remove it.
    (cert (var? var)) 
    (let-values ([(simplified recheck) (simplify-unification var-c (list (cons var val)))]) ;TODO return val constraint to simplify it with potentially other bindings and also unbind its var?
      (if (or (fail? simplified) (fail? recheck)) (values fail fail fail failure) ; (if (succeed? val-c) s (unbind-constraint s val))
	  (values (cons (cons var val) bindings) simplified recheck (extend s var val)))))

  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (cert (state? s) (not (eq? x y)))
    (set-state-substitution
     s (sbral-set-ref
	(state-substitution s)
	(fx- (sbral-length (state-substitution s)) (var-id x)) y unbound)))

  (org-define (simplify-unification g s)
    (cert (goal? g))
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (simplify-unification (conj-lhs g) s)])
		  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
		   (let-values ([(simplified-rhs recheck-rhs) (simplify-unification (conj-rhs g) s)])
		     (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
     [(disj? g) (let*-values ([(simplified-lhs recheck-lhs) (simplify-unification (disj-lhs g) s)]
			      [(lhs) (conj simplified-lhs recheck-lhs)])
		  (if (succeed? lhs) (values succeed succeed)
		      (let*-values ([(simplified-rhs recheck-rhs) (simplify-unification (disj-rhs g) s)]
				    [(rhs) (conj simplified-rhs recheck-rhs)])
			
			(if (or (fail? simplified-lhs) (not (succeed? recheck-lhs)) ;TODO if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked
				(and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
				     (conj-memp simplified-lhs (lambda (g) (or (==? g) (and (matcho? g) (null? (matcho-out-vars g))))))))
			    (values succeed (disj-factorized lhs rhs))
			    (values (disj-factorized lhs rhs) succeed)))))]
     [(==? g) (let-values ([(s simplified recheck) (mini-simplify s (==-lhs g) (==-rhs g) succeed succeed)])
		(values simplified recheck))
      
      #;
      (let ([s^ (mini-unify s (==-lhs g) (==-rhs g))])
		(if (failure? s^) (values fail fail)
		    (values (mini-diff s^ s) succeed)))]
     #;
     (let-values ([(_ simplified recheck) (mini-simplify s (==-lhs g) (==-rhs g) succeed succeed)])
		(values simplified recheck))
     [(noto? g) (let-values ([(simplified recheck) (simplify-unification (noto-goal g) s)])
		  (if (succeed? recheck) (values (noto simplified) succeed)
		      (values succeed (noto (conj simplified recheck)))))]
     [(pconstraint? g) (simplify-unification/pconstraint g s (pconstraint-vars g) #t)]
     [(constraint? g) (simplify-unification (constraint-goal g) s)]
     [(procedure? g) (values succeed g)]
     [(matcho? g)
      (let-values ([(normalized out-vars) (mini-reify-normalized s (matcho-out-vars g))]
		   [(_ in-vars) (mini-reify-normalized s (matcho-in-vars g))])
       (let ([g (normalize-matcho out-vars in-vars (matcho-goal g))])
	 (cond
	  [(fail? g) (values fail fail)] ; TODO in simplify matcho, can i just return the g case and let one fail be enough?
	  [(and normalized (not (null? (matcho-out-vars g)))) (values g succeed)]
	  [(null? (matcho-out-vars g)) (let-values ([(_ g s^ p) (expand-matcho g empty-state empty-package)])
					 (simplify-unification g s))] ; TODO should we thread the real state when expanding matcho while simplifying ==?
	  [else (values succeed g)])))]
     [else (assertion-violation 'simplify-unification "Unrecognized constraint type" g)]))
  
  (define (simplify-unification/pconstraint g s vars normalized) ;TODO refactor pconstraint solving/simplifying to share var iteration code among impls
    (if (null? vars)
	(if normalized (values g succeed) (values succeed g)) 
	(let-values ([(normalized-var walked) (mini-walk-normalized s (car vars))])
	  (if (eq? (car vars) walked)
	      (simplify-unification/pconstraint g s (cdr vars) (and normalized normalized-var)) ;TODO make == simplifier for pconstraints check for new vars
	      (simplify-unification ((pconstraint-procedure g) (car vars) walked g succeed (pconstraint-data g)) s))))
#;
    (values succeed (if (memq v (pconstraint-vars g)) ((pconstraint-procedure g) v x (pconstraint-data g)) g)))

  ;; === DISUNIFICATION ===
  
  (define (disunify s x y)
    ;; Specialized unification for =/= constraints. Only solves enough to confirm non failure and simplifies using special routines for =/=.
    (cert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-var-val s x)]
		 [(y-var y) (walk-var-val s y)]) ;TODO how does disunify play with constraints in substitution?
      (if (eq? x-var y-var) (values fail fail) ; The same variable is never =/= itself regardless of value or constraint.
	  (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
	      (disunify-binding s y-var y x-var x)
	      (disunify-binding s x-var x y-var y)))))

  (define (disunify-binding s x-var x y-var y) ; if x-var and y-var are both vars, x-var has a lower index
	      (cert (state? s)) ; -> goal?(disequality) goal?(constraint)
    (cond
     [(goal? x) (values (=/= x-var (if (goal? y) y-var y)) x)] ; Return the constraint on x to recheck for possible == to commit.
     [(goal? y) (if (var? x)
		    (values (=/= x y-var) succeed) ; x is older so it controls the constraints that may pertain to x=/=y. This is a function of the disunifier assigning x=/=y goals to x. If a constraint that might unify could be solved by x=/=y, it would already be attributed to x. Therefore, we only need to add the x=/=y constraint. There is nothing to recheck.
		    (values (=/= y-var x) y))] ; Since x is a value here, treat y like the dominant constraint and simplify it.
     [(eq? x y) (values fail fail)]
     [(var? x) (values (=/= x y) succeed)]
     [(var? y) (values (=/= y x) succeed)]
     [(and (pair? x) (pair? y))
      (let-values ([(lhs c) (disunify s (car x) (car y))])
	(exclusive-cond
	 [(succeed? lhs) (values succeed succeed)] ; TODO test whether all the manual checks for fail/succeed could be replaced by conj/disj macros
	 [(fail? lhs) (disunify s (cdr x) (cdr y))]
	 [else (values (disj lhs (=/= (cdr x) (cdr y))) c)]))]
     [else (values succeed succeed)]))
  
  ;; === CONSTRAINTS ===
  
  (org-define (state-add-constraint s c vs) ;TODO consider sorting ids of variables before adding constraints to optimize adding to sbral. or possibly writing an sbral multi-add that does one pass and adds everything. would work well with sorted lists of attr vars to compare which constraints we can combine while adding
    (cert (state? s) (goal? c) (list? vs))
    ;let-values ([(s c) (if (null? (cdr vs)) (values s c) (values (state-extend-store s c) c))]) ; Proxy constraints with multiple attributed variables so that they only need to be solved once by whichever variable is checked first and can be removed from the global store so subsequent checks will simply succeed. 
    (fold-left (lambda (s v)
		 #;
		 (when (not (goal? (substitution-ref (state-substitution s) v))) (printf "instore: ~a~%var: ~a~%new con: ~a~%" (substitution-ref (state-substitution s) v) v c)
		       (pretty-print c))
		 (let ([val-or-goal (substitution-ref (state-substitution s) v)]) ; Since all attributed vars should be normalized, we don't need walk - we can look them up directly in the substitution.

		   (when (not (goal? val-or-goal))
		     (pretty-print v)
		     (pretty-print val-or-goal)
		     (pretty-print (walk s v))
		     #;
		     (let ([ms (goal-memp c matcho?)])
		       (pretty-print (list (list-ref ms 3) (list-ref ms 4) (equal? (matcho-goal (list-ref ms 3)) (matcho-goal (list-ref ms 6)))))
		       (pretty-print ms))
		     (pretty-print c)
		     (pretty-print s)
		     
				     )
		   (cert (goal? val-or-goal)) ;TODO can we store stale constraints?
		   (if (goal? val-or-goal) (extend s v (conj val-or-goal c)) s))
#;;TODO clean up state add constraint. remove dead code
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left make-conj succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))

  (define (unbind-constraint s v) ;TODO rename unbind-constraint -> remove-constraint
    (extend s v unbound)))
