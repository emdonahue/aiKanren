(library (state) ; Main state object that holds substitution & constraints
  (export reify reify-var instantiate-var walk state-add-constraint get-constraints remove-constraints unify disunify walk-var walk-var-val extend unbind-constraint) ;;TODO double check state exports. remove extend at least
  (import (chezscheme) (store) (sbral) (datatypes) (negation) (utils))

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
		 [w (reify-constraint (state-constraints s) w)])
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
    (let-values ([(binding v) (walk-binding (state-substitution s) v)]) v))

  (define (walk-var s v)
    (let-values ([(binding v) (walk-binding (state-substitution s) v)]) (if (goal? v) binding v)))

  (define (walk-var-val s v)
    (walk-binding (state-substitution s) v))

  (org-define (walk-constraint s v)
    (cert (state? s) (var? v))
    (let-values ([(binding v) (walk-binding (state-substitution s) v)])
      (org-printf "walk constraint")
      (cert (or (var? v) (goal? v))) ;TODO can we remove walk-constraint since succeed is the new unbound?
      (if (var? v) succeed v)))
  
  (define (walk-binding s v)
    (cert (sbral? s) (not (and (var? v) (zero? (var-id v)))))
    (if (var? v)
	(let ([walked (sbral-ref
		       s
		       (fx- (sbral-length s) (var-id v)) ; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
		       unbound)])
	  ;(printf "walked ~s ~s ~%" v walked)
	  (exclusive-cond
	   [(unbound? walked) (values v v)]
	   [(var? walked) (walk-binding s walked)]
	   [else (values v walked)]))
	(values v v)))

  ;; === UNIFICATION ===
  
  (define (unify s x y) ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system. The substitution also contains constraints on the variable, which must be dealt with by the unifier.
	      (cert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)]
		 [(y-var y) (walk-binding (state-substitution s) y)])
      (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
	  (unify-binding s y-var y x-var x)
	  (unify-binding s x-var x y-var y))))

  (define (unify-binding s x-var x y-var y) ; If both vars, x-var guaranteed to have lower id
    (cert (not (or (goal? x-var) (goal? y-var))))
    (cond
       [(goal? x) ; TODO When should simplifying a constraint commit more ==?
	(if (goal? y) (if (eq? x-var y-var) (values succeed succeed s) (extend-constraint s x-var y-var x y)) ; x->y, y->y, ^cx(y)&cy
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
    (cert (state? s) (not (eq? x y)))
    (set-state-substitution
     s
     (sbral-set-ref
      (state-substitution s)
      (fx- (sbral-length (state-substitution s)) (var-id x)) y unbound)))

  (define (simplify-unification g v x) ;TODO simplifiers need more thorough testing
    (cert (goal? g) (var? v)) ;TODO separate into conj and disj simplifier. conj can assume all primitive constraints attribute to var. disj simplifier has to check
    (exclusive-cond
     [(conj? g) (conj (simplify-unification (conj-lhs g) v x)
		      (simplify-unification (conj-rhs g) v x))]
     [(disj? g) (disj (simplify-unification (disj-lhs g) v x) ;TODO consider only simplifying part of disj to guarantee that analyzed constraints attribute to the currently unified pair.
		      (simplify-unification (disj-rhs g) v x))]
     [(==? g) (if (eq? v (==-lhs g)) (== x (==-rhs g)) g)]
     [(noto? g) (noto (simplify-unification (noto-goal g) v x))]
     [(pconstraint? g) (if (memq v (pconstraint-vars g)) ((pconstraint-procedure g) v x (pconstraint-data g)) g)]
     [else g]))

  ;; === DISUNIFICATION ===
  
  (define (disunify s x y)
    ;; Specialized unification for =/= constraints. Only solves enough to confirm non failure and simplifies using special routines for =/=.
	      (cert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)]
		 [(y-var y) (walk-binding (state-substitution s) y)]) ;TODO how does disunify play with constraints in substitution?
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
  
  (org-define (state-add-constraint s c vs) ;TODO consider sorting ids of variables before adding constraints to optimize adding to sbral
    (cert (state? s) (goal? c) (list? vs))
    (fold-left (lambda (s v)
		 (extend s v (conj (walk-constraint s v) c))
		 #;;TODO clean up state add constraint. remove dead code
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left make-conj succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))

  (define (unbind-constraint s v) ;TODO rename unbind-constraint -> remove-constraint
    (extend s v unbound)))
