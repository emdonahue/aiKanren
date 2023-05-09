(library (substitution)
  (export empty-substitution walk unify make-var var? var-id extend)
  (import (chezscheme) (sbral) (var) (failure) (datatypes))

  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v) 1) unbound)])
	  (if (unbound? walked) v (walk s walked)))
	v))

  ;;TODO thread disequalities monadically and bubble constant disequalities to the top to deprioritize double var constraints
  (define (unify s x y)
    (assert (substitution? s)) ; -> substitution? ((var? . val) ...)
    (let ([x (walk s x)] [y (walk s y)])
      (cond
       [(eq? x y) (values s '())]
       [(and (var? x) (var? y))
	(cond
	 [(< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y) (values s '())] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (extend s y x)])]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
	(let-values
	    ([(s car-extensions) (unify s (car x) (car y))])
	  (if (failure? s)
	      (values failure '())
	      (let-values ([(s cdr-extensions) (unify s (cdr x) (cdr y))])
		(values s (append car-extensions cdr-extensions)))))]
       [else (values failure '())])))

  #;
  (define (unify s x y)
    (assert (substitution? s)) ; -> substitution? ((var? . val) ...)
    (let ([x (walk s x)] [y (walk s y)])
      (cond
       [(eq? x y) (values s succeed)]
       [(and (var? x) (var? y))
	(cond
	 [(< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y) (values s succeed)] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
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
    ;;TODO test whether checking constraints after every extension is faster than checking all constraints at the end
    (values
     (make-substitution
      (sbral-set-ref
       (substitution-dict s)
       (- (sbral-length (substitution-dict s)) (var-id x) 1) y unbound)) (list (cons x y))))

  #;
    (define (extend s x y)
    ;;TODO test whether checking constraints after every extension is faster than checking all constraints at the end
    (values
     (make-substitution
      (sbral-set-ref
       (substitution-dict s)
       (- (sbral-length (substitution-dict s)) (var-id x) 1) y unbound)) (== x y))))
