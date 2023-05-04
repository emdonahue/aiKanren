(library (substitution)
  (export substitution-empty walk make-var var? var-id extend)
  (import (chezscheme) (sbral))

  (define-structure (var id))
  (define-structure (substitution dict))
  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  (define substitution-empty (make-substitution sbral-empty))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v) 1) unbound)])
	  (if (unbound? walked) v (walk s walked)))
	v))

  (define (extend s x y)
    (make-substitution
     (sbral-set-ref
      (substitution-dict s)
      (- (sbral-length (substitution-dict s)) (var-id x) 1) y unbound))))
