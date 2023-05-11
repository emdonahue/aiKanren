(library (state)
  (export reify unify instantiate-var walk constrain)
  (import (chezscheme) (prefix (substitution) substitution:) (var) (failure) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (substitution:walk (state-substitution s) v)]
	    [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))
  
  (define (unify s x y)
    (assert (state? s))
    (substitution:unify (state-substitution s) x y))

  (define (walk s v)
    (substitution:walk (state-substitution s) v))

  (define (constrain s v c)
    (assert (and (state? s) (var? v) (goal? c)))
    
    ))
