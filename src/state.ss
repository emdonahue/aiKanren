(library (state)
  (export reify unify instantiate-var walk)
  (import (chezscheme) (except (substitution) unify walk) (prefix (only (substitution) unify walk) substitution:) (var) (failure) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let ([v (substitution:walk (state-substitution s) v)])
	(if (var? v) (get-constraint (state-constraints s) v v)
	    (reify s v)))]
     [else v]))
  
  (define (unify s x y)
    (assert (state? s))
    (substitution:unify (state-substitution s) x y))

  (define (walk s v)
    (substitution:walk (state-substitution s) v)))
