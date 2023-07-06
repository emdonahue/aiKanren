(library (state) ; Main state object that holds substitution & constraints
  (export reify instantiate-var walk state-add-constraint print-substitution get-constraints remove-constraints unify disunify) ;;TODO double check state exports. remove extend at least
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

  ;; constraint x var - simplify, extend var - handled by var  
  ;; constraint x constant - 
  ;; constraint x pair - simplify constraint with constant, extend var with constant
  ;; constraint x constraint - extend lesser var with greater, simplify greater constraint with lesser, store conjoint constraints in greater, return success and state with both
  
  (org-define (unify s x y) ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)] [(y-var y) (walk-binding (state-substitution s) y)])
      (org-cond
       [(goal? x)
	(if (goal? y)
	    (org-exclusive-cond double-constraint
	     [(fx< (var-id x-var) (var-id y-var)) (unify-constraints s x-var x y-var y)]
	     [(var-equal? x y) (values succeed succeed s)]
	     [else (unify-constraints s y-var y x-var x)])
	    (unify-constraint s x-var x y-var y))] ; TODO When should simplifying a constraint commit more ==?
       [(eq? x y) (values succeed succeed s)]
       [(goal? y) (unify-constraint s y-var y x-var x)]
       [(var? x)
	(if (var? y)
	    (cond
	     [(fx< (var-id x) (var-id y)) (extend-var s x y)]
	     [(var-equal? x y)
	      (values succeed succeed s)] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	     [else (extend-var s y x)])
	    (extend-var s x y))]
       [(var? y) (extend-var s y x)]
       [(and (pair? x) (pair? y)) ;TODO test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify
	(let-values
	    ([(g c s) (unify s (car x) (car y))])
	  (if (fail? g)
	      (values fail fail failure)
	      (let-values ([(g^ c^ s) (unify s (cdr x) (cdr y))])
		(values (conj g g^) (conj c c^) s))))] ; TODO make unifier normalize?
       [else (values fail fail failure)])))

  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (set-state-substitution
     s
     (sbral-set-ref
      (state-substitution s)
      (fx- (sbral-length (state-substitution s)) (var-id x)) y unbound)))
  
  (define (extend-var s x y)
    ;; Insert a new binding between x and y into the substitution.
    (values (== x y) succeed (extend s x y)))

  (org-define (unify-constraint s x-var x y-var y)
    (assert (and (state? s) (var? x-var) (goal? x) (not (goal? y))))
    (if (var? y)
	(org-exclusive-cond
	 [(fx< (var-id x-var) (var-id y-var)) (values (== x-var y-var) (simplify-constraint x x-var y-var) (extend s x-var y-var))]
	 [(var-equal? x y) (values succeed succeed s)]
	 [else (values (== y x-var) x (extend s y x-var))])
	(values (== x-var y) (simplify-constraint x x-var y) (extend s x-var y))))

  (define (unify-constraints s x-var x y-var y)
    (values (== x-var y-var) (conj (simplify-constraint x x-var y-var) y) (extend s x-var y-var)))

  #;
  (define (extend-constraint s x-var x y-var y)
    (assert (and (state? s) (var? x-var) (goal? x) (var? y-var) (var? y)))
    (if (var? y)
	(values succeed (conj (simplify-constraint x x-var y) (extend s x-var y)))
	))
  
  ;; === CONSTRAINTS ===

  (org-define (simplify-constraint g v x)
    (assert (and (goal? g) (var? v)))
    (exclusive-cond
     [(==? g)
      (assert (equal? (==-lhs g) v))
      (== x (==-rhs g))]
     [(noto? g) (noto (simplify-constraint (noto-goal g) v x))]
     [(pconstraint? g) (if (var? x) (pconstraint (cons x (remove v (pconstraint-vars g))) (pconstraint-procedure g) (pconstraint-type g)) ((pconstraint-procedure g) v x))]
     [else (assertion-violation 'simplify-constraint "Unrecognized constraint type" g)]))
  
  (define (state-add-constraint s c vs)
    (assert (and (state? s) (goal? c) (list? vs)))
    (fold-left (lambda (s v)
		 (extend s v (conj (walk-constraint s v) c))
		 #;;TODO clean up state add constraint. remove dead code
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left make-conj succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))

  (define (disunify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)]
		 [(y-var y) (walk-binding (state-substitution s) y)]) ;TODO how does disunify play with constraints in substitution?
      (assert (and (not (goal? x)) (not (goal? y))))
      (cond
       [(eq? x y) fail]
       [(var? x)
	(if (var? y)
	    (cond
	     [(fx< (var-id x) (var-id y)) (noto (== x y))]
	     [(var-equal? x y) ;TODO test swapping var-equal? with another fx> check and making it the else case
	      fail] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	     [else (noto (== y x))])
	    (noto (== x y)))]
       [(var? y) (noto (== y x))]
       [(and (pair? x) (pair? y)) ;TODO test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify
	(let ([lhs (disunify s (car x) (car y))])
	  (cond
	   [(succeed? lhs) succeed] ; TODO test whether all the manual checks for fail/succeed could be replaced by conj/disj macros
	   [(fail? lhs) (disunify s (cdr x) (cdr y))]
	   [else (disj lhs (noto (== (cdr x) (cdr y))))]))]
       [else succeed])))
  
   ;; === DEBUGGING ===

  (define (print-substitution s)
    (map (lambda (p) (cons (make-var (fx- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))
