(library (state) ; Main state object that holds substitution & constraints
  (export reify instantiate-var walk state-add-constraint print-substitution get-constraints remove-constraints unify) ;;TODO double check state exports
  (import (chezscheme) (store) (sbral) (datatypes))

  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  ;; === VARIABLES ===
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (walk s v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))

  (define (walk s v)
    (if (var? v)
	(let ([walked (sbral-ref
		       (state-substitution s)
		       (- (sbral-length (state-substitution s)) (var-id v)) ; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
		       unbound)]) 
	  (if (unbound? walked) v (walk s walked)))
	v))

  ;; === UNIFICATION ===
  
  (define (unify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    (assert (state? s)) ; -> substitution? goal?
    (let ([x (walk s x)] [y (walk s y)])
      (cond
       [(eq? x y) (values succeed s)]
       [(and (var? x) (var? y))
	(cond
	 [(< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y) (assert #f) (values succeed s)] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (extend s y x)])]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
	(let-values
	    ([(car-extensions s) (unify s (car x) (car y))])
	  (if (failure? s)
	      (values fail failure)
	      (let-values ([(cdr-extensions s) (unify s (cdr x) (cdr y))])
		(values (normalized-conj* car-extensions cdr-extensions) s))))] ; TODO make unifier normalize?
       [else (values fail failure)])))
  
  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (values
     (== x y)
     (set-state-substitution s
      (sbral-set-ref
       (state-substitution s)
       (- (sbral-length (state-substitution s)) (var-id x)) y unbound))))

  ;; === CONSTRAINTS ===

  (define (state-add-constraint s c vs)
    (assert (and (state? s) (goal? c) (list? vs)))
    (fold-left (lambda (s v)
		 (set-state-constraints s (add-constraint (state-constraints s) v c))) s vs))

  (define (get-constraints s vs)
    (fold-left normalized-conj* succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))
  
   ;; === DEBUGGING ===

  (define (print-substitution s)
    (map (lambda (p) (cons (make-var (- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))
