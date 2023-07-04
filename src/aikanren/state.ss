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

  ;; constraint x var - extend var - handled by var
  
  ;; constraint x constant - simplify var
  ;; constraint x pair - simplify var
  ;; constraint x constraint - simplify one and extend the var of the other
  
  (org-define (unify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-binding (state-substitution s) x)] [(y-var y) (walk-binding (state-substitution s) y)])
      (org-cond
       [(and (eq? x y) (not (goal? y))) (values succeed s)]
       [(and (var? x) (var? y))
	(cond
	 [(fx< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y)
	  (values succeed s)] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (extend s y x)])]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(goal? x)
	(if (goal? y)
	    (assert #f)
	    (values (simplify-constraint x x-var y) (extend2 s x-var y)))] ; TODO When should simplifying a constraint commit more ==?
       [(and (pair? x) (pair? y)) ;TODO test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify
	(let-values
	    ([(car-extensions s) (unify s (car x) (car y))])
	  (if (failure? s)
	      (values fail failure)
	      (let-values ([(cdr-extensions s) (unify s (cdr x) (cdr y))])
		(values (conj car-extensions cdr-extensions) s))))] ; TODO make unifier normalize?
       [else (values fail failure)])))
  
  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (values
     (== x y)
     (set-state-substitution s
      (sbral-set-ref
       (state-substitution s)
       (fx- (sbral-length (state-substitution s)) (var-id x)) y unbound))))

  
  (define (extend2 s x y) ;TODO merge extend2
    ;; Insert a new binding between x and y into the substitution.
    (set-state-substitution
     s
     (sbral-set-ref
      (state-substitution s)
      (fx- (sbral-length (state-substitution s)) (var-id x)) y unbound)))
  
  
  ;; === CONSTRAINTS ===

  (org-define (simplify-constraint g v x)
    (assert (and (goal? g) (var? v) (not (var? x))))
    (exclusive-cond
     [(==? g)
      (assert (equal? (==-lhs g) v))
      (== x (==-rhs g))]
     [(noto? g) (noto (simplify-constraint (noto-goal g) v x))]
     [else (assertion-violation 'simplify-constraint "Unrecognized constraint type" g)]))
  
  (define (state-add-constraint s c vs)
    (assert (and (state? s) (goal? c) (list? vs)))
    (fold-left (lambda (s v)
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left make-conj succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))

  (define (disunify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let ([x (walk s x)] [y (walk s y)])
      (cond
       [(eq? x y) fail]
       [(and (var? x) (var? y))
	(cond
	 [(fx< (var-id x) (var-id y)) (noto (== x y))]
	 [(var-equal? x y)
	  fail] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (noto (== y x))])]
       [(var? x) (noto (== x y))]
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
