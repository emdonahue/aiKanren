(library (substitution)
  (export empty-substitution walk unify make-var var? var-id extend)
  (import (chezscheme) (sbral) (var))

  (define-structure (substitution dict))
  (define empty-substitution (make-substitution sbral-empty))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v) 1) unbound)])
	  (if (unbound? walked) v (walk s walked)))
	v))

  (define (unify s x y)
     (cond
      [(not s) #f]
      [else (let ([x (walk s x)] [y (walk s y)])
	      (cond
	       [(eq? x y) s]
	       [(and (var? x) (var? y))
		(cond
		 [(< (var-id x) (var-id y)) (extend s x y)]
		 [(= (var-id x) (var-id y)) s] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
		 [else (extend s y x)])]
	       [(var? x) (extend s x y)]
	       [(var? y) (extend s y x)]
	       [(and(pair? x) (pair? y))
		(unify (unify s (car x) (car y)) (cdr x) (cdr y))]
	       [else #f]))]))

  (define (extend s x y)
    (make-substitution
     (sbral-set-ref
      (substitution-dict s)
      (- (sbral-length (substitution-dict s)) (var-id x) 1) y unbound))))
