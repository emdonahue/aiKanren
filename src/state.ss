(library (state)
  (export reify instantiate-var walk) ;;TODO double check state exports
  (import (chezscheme) (prefix (substitution) substitution:) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (substitution:walk (state-substitution s) v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))

  

  (define (walk s v)
    (substitution:walk (state-substitution s) v))

)
