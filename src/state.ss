(library (state)
  (export reify instantiate-var walk state-add-constraint print-substitution get-constraints remove-constraints) ;;TODO double check state exports
  (import (chezscheme) (prefix (substitution) substitution:) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (substitution:walk (state-substitution s) v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))

  (define (state-add-constraint s v c)
    (assert (and (state? s) (var? v) (goal? c)))
    (set-state-constraints s (add-constraint (state-constraints s) v c)))

  (define (walk s v)
    (substitution:walk (state-substitution s) v))

  (define (get-constraints s vs)
    (fold-left normalized-conj* succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))
  
  (define (print-substitution s)
    (substitution:print-substitution (state-substitution s)))

  (define (unify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    ;;TODO thread disequalities monadically and bubble constant disequalities to the top to deprioritize double var constraints
    (assert (state? s)) ; -> substitution? goal?
    (let ([x (walk s x)] [y (walk s y)])
      (cond
       [(eq? x y) (values s succeed)]
       [(and (var? x) (var? y))
	(cond
	 [(< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y) (assert #f) (values s succeed)] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (extend s y x)])]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
	(let-values
	    ([(s car-extensions) (unify s (car x) (car y))])
	  (if (failure? s)
	      (values failure fail)
	      (let-values ([(s cdr-extensions) (unify s (cdr x) (cdr y))])
		(values s (normalized-conj* car-extensions cdr-extensions)))))] ; TODO make unifier normalize?
       [else (values failure fail)]))))
