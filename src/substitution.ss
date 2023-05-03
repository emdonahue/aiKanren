(library (substitution)
  (export substitution-empty walk unify make-var)
  (import (chezscheme) (sbral))

  (define-structure (var id))
  (define (var-equal? x y) (= (var-id x) (var-id y)))
  
  (define-structure (substitution dict))
  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  (define substitution-empty (make-substitution sbral-empty))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v)) unbound)])
	  (if (or (unbound? walked) (var-equal? v walked)) v (walk s v)))
	v))

  (trace-define (extend s x y)
    (make-substitution
     (sbral-set-ref
      (substitution-dict s)
      (- (sbral-length (substitution-dict s)) (var-id x))  y unbound)))
  
  (trace-define (unify x y s)
    (let ([x (walk s x)]
	  [y (walk s y)])
      (cond
       [(eq? x y) s]
       [(and (var? x) (var? y)) (assert #f)]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)])
      )
    ))
