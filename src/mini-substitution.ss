(library (mini-substitution)
  (export mini-walk mini-unify)
  (import (chezscheme) (datatypes))


  (define (mini-walk s v)
    (if (var? v)
	(let ([b (assq v s)])
	  (if b (mini-walk s (cdr b)) v))
	v))

  (define (mini-unify s x y)
    (let ([x (mini-walk s x)] [y (mini-walk s y)])
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
	    ([(s car-extensions) (mini-unify s (car x) (car y))])
	  (if (failure? s)
	      (values failure fail)
	      (let-values ([(s cdr-extensions) (mini-unify s (cdr x) (cdr y))])
		(values s (normalized-conj* car-extensions cdr-extensions)))))] ; TODO make unifier normalize?
       [else (values failure fail)])))

  (define (extend s x y)
    (cons (cons x y) s)))
