(library (substitution)
  (export empty-substitution walk unify make-var var? var-id extend print-substitution)
  (import (chezscheme) (sbral) (datatypes))

  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v)) unbound)]) ; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
	  (if (unbound? walked) v (walk s walked)))
	v))

  (define (unify s x y)
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system.
    ;;TODO thread disequalities monadically and bubble constant disequalities to the top to deprioritize double var constraints
    (assert (substitution? s)) ; -> substitution? goal?
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
		(values s (conj* car-extensions cdr-extensions)))))]
       [else (values failure fail)])))

  (define (extend s x y)
    (values
     (make-substitution
      (sbral-set-ref
       (substitution-dict s)
       (- (sbral-length (substitution-dict s)) (var-id x)) y unbound)) (== x y)))

  (define (print-substitution s)
    (let ([sbral (substitution-dict s)])
      (map (lambda (p) (cons (make-var (- (sbral-length sbral) (car p))) (cdr p))) (sbral->alist sbral)))))
