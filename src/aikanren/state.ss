(library (state) ; Main state object that holds substitution & constraints
  (export reify instantiate-var walk state-add-constraint print-substitution get-constraints remove-constraints unify disunify walk-var) ;;TODO double check state exports. remove extend at least
  (import (chezscheme) (store) (sbral) (datatypes) (negation) (utils))

  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  ;; === VARIABLES ===
  
  (define (reify s v)
    ;;TODO support cyclic terms in reifier
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (walk s v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))

  (define (walk s v)
    (assert (state? s))
    (let-values ([(binding v) (walk-binding (state-substitution s) v)]) v))

  (define (walk-var s v)
    (let-values ([(binding v) (walk-binding (state-substitution s) v)]) (if (goal? v) binding v)))

  (define (walk-constraint s v)
    (assert (and (state? s) (var? v)))
    (let-values ([(binding v) (walk-binding (state-substitution s) v)])
      (assert (or (var? v) (goal? v)))
      (if (var? v) succeed v)))
  
  (define (walk-binding s v)
    (assert (sbral? s))
    (if (var? v)
	(let ([walked (sbral-ref
		       s
		       (fx- (sbral-length s) (var-id v)) ; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
		       unbound)])
	  (exclusive-cond
	   [(unbound? walked) (values v v)]
	   [(var? walked) (walk-binding s walked)]
	   [else (values v walked)]))
	(values v v)))

  ;; === UNIFICATION ===
  
  (org-define (unify s x y) ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system. The substitution also contains constraints on the variable, which must be dealt with by the unifier.
    (assert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)]
		 [(y-var y) (walk-binding (state-substitution s) y)])
      (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
	  (unify-binding s y-var y x-var x)
	  (unify-binding s x-var x y-var y))))

  (define (unify-binding s x-var x y-var y) ; If both vars, x-var guaranteed to have lower id
    (org-cond
       [(goal? x) ; TODO When should simplifying a constraint commit more ==?
	(if (goal? y) (extend-constraint s x-var y-var x y) ; x->y, y->y, ^cx(y)&cy
	    (extend-constraint s x-var y x succeed))] ; x->y, ^cx(y). y always replaces x if x var, no matter whether y var or const
       [(eq? x y) (values succeed succeed s)]
       [(goal? y) (if (var? x)
		      (extend-constraint s x y-var succeed y) ; x->y, y->y, ^cy. y always replaces x due to id, 
		      (extend-constraint s y-var x y succeed))] ; y->x, ^cy(x). unless x is a constant.
       [(var? x) (extend-var s x y)]
       [(var? y) (extend-var s y x)]
       [(and (pair? x) (pair? y)) ;TODO test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify
	(let-values
	    ([(g c s) (unify s (car x) (car y))])
	  (if (fail? g)
	      (values fail fail failure)
	      (let-values ([(g^ c^ s) (unify s (cdr x) (cdr y))])
		(values (conj g g^) (conj c c^) s))))]
       [else (values fail fail failure)]))
  
  (define (extend-var s x y)
    ;; Insert a new binding between x and y into the substitution.
    (values (== x y) succeed (extend s x y)))

  (define (extend-constraint s var val var-c val-c)
    ;; Opportunistically simplifies the retrieved constraints using the available vars and vals and then extends the substitution. If there is a constraint on val (and it is a var), we must explicitly remove it.
    (let ([c (simplify-unification var-c var val)])
      (if (fail? c) (values fail fail failure)
	  (values (== var val) (conj c val-c) (extend (if (succeed? val-c) s (unbind-constraint s val)) var val)))))

  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (set-state-substitution
     s
     (sbral-set-ref
      (state-substitution s)
      (fx- (sbral-length (state-substitution s)) (var-id x)) y unbound)))

  (org-define (simplify-unification g v x) ;TODO simplifiers need more thorough testing
    (assert (and (goal? g) (var? v)))
    (exclusive-cond
     [(conj? g) (conj (simplify-unification (conj-lhs g) v x)
		      (simplify-unification (conj-rhs g) v x))]
     [(disj? g) (disj (simplify-unification (disj-lhs g) v x) ;TODO consider only simplifying part of disj to guarantee that analyzed constraints attribute to the currently unified pair.
		      (simplify-unification (disj-rhs g) v x))]
     [(==? g) (if (eq? v (==-lhs g)) (== x (==-rhs g)) g)]
     [(noto? g) (noto (simplify-unification (noto-goal g) v x))]
     [(pconstraint? g) (if (memq v (pconstraint-vars g)) ((pconstraint-procedure g) v x) g)]
     [else g]))

  ;; === DISUNIFICATION ===
  
  (org-define (disunify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)]
		 [(y-var y) (walk-binding (state-substitution s) y)]) ;TODO how does disunify play with constraints in substitution?
      (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
	  (disunify-binding s y-var y x-var x)
	  (disunify-binding s x-var x y-var y))))

  (define (disunify-binding s x-var x y-var y) ; if x-var and y-var are both vars, x-var has a lower index
    (cond
     [(goal? x)
      (if (may-unify x x-var) ; We only need to recheck goals that may unify what this =/= disunifies, as other constraints will never fail.
	  (values (=/= x-var (if (goal? y) y-var y)) x (unbind-constraint s x-var)) ;TODO can we extract only the subgoals that may unify when solving a =/= in disunify
	  (values (=/= x-var (if (goal? y) y-var y)) succeed s))]
     [(goal? y) (if (var? x)
		    (values (=/= x y-var) succeed s) ; x is lower id, so it controls the constraints that may pertain to x=/=y. Therefore, we only need to add a constraint. There is nothing to check.
		    (let ([c (simplify-disunification y y-var x)])
		      (org-exclusive-cond y-goal-x-val
		       [(fail? c) (values fail fail failure)]
		       [(succeed? c) (values succeed succeed s)]
		       [(eq? c y) (values (=/= y-var x) succeed s)]
		       [else (values (=/= y-var x) c (unbind-constraint s y-var))])))]
     [(eq? x y) (values fail fail failure)]
     [(var? x) (values (=/= x y) succeed s)]
     [(var? y) (values (=/= y x) succeed s)]
     [(and (pair? x) (pair? y))
      (let-values ([(lhs c s^) (disunify s (car x) (car y))])
	(exclusive-cond
	 [(succeed? lhs) (values succeed succeed s)] ; TODO test whether all the manual checks for fail/succeed could be replaced by conj/disj macros
	 [(fail? lhs) (disunify s (cdr x) (cdr y))]
	 [else (values (disj lhs (=/= (cdr x) (cdr y))) c s^)]))]
     [else (values succeed succeed s)]))

  (define (may-unify g v)
    ;; #t if this constraint contains a == containing var v, implying that it might fail or collapse if we conjoin a =/= assigned to v.
    (exclusive-cond
     [(==? g) (equal? (==-lhs g) v)] ; Existing constraints are already normalized, so only lhs need be checked.
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-car (disj-cdr g)) v))] ; If the disjunction has 2 disjuncts without v, it can neither fail nor collapse.
     [else #f]))

  (define (simplify-disunification g var val) ;x=/=10.  x==10->fail x==3->abort x==y, ignore. ;x=/=10->abort
    ;; Simplifies a constraint with the information that var =/= val
    (exclusive-cond ;TODO should we check multiple directions during simplification for unnormalized disjuncts?
     [(conj? g) (conj (simplify-disunification (conj-lhs g) var val)
		      (simplify-disunification (conj-rhs g) var val))]
     [(disj? g) (disj (simplify-disunification (disj-lhs g) var val) ;TODO consider only simplifying part of disj to guarantee that analyzed constraints attribute to the currently unified pair.
		      (simplify-disunification (disj-rhs g) var val))]
     [(==? g) (if (eq? var (==-lhs g)) ; If the == is on the same variable as the =/=,
		  (if (equal? val (==-rhs g)) ; and it has an equal value,
		      fail ; fail. Otherwise, 
		      (if (or (var? (==-rhs g)) (var? val)) g succeed)) ; succeed if both are ground (since they are not eq?)
		  g)] ; Ignore constraints on unrelated variables.
     [(noto? g) (if (==? (noto-goal g))
		    (if (and (eq? val (==-rhs (noto-goal g))) ; =/= only cancel each other if identical
			     (eq? val (==-rhs (noto-goal g))))
			succeed g) g)] ; TODO should we simplify pconstraints during disunification
     [else g]))
  
  ;; === CONSTRAINTS ===
  
  (define (state-add-constraint s c vs) ;TODO consider sorting ids of variables before adding constraints to optimize adding to sbral
    (assert (and (state? s) (goal? c) (list? vs)))
    (fold-left (lambda (s v)
		 (extend s v (conj (walk-constraint s v) c))
		 #;;TODO clean up state add constraint. remove dead code
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left make-conj succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))

  (define (unbind-constraint s v) ;TODO rename unbind-constraint -> remove-constraint
    (extend s v unbound))
  
   ;; === DEBUGGING ===

  (define (print-substitution s)
    (map (lambda (p) (cons (make-var (fx- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))
