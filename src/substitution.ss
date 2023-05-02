(library (substitution)
  (export substitution-empty walk unify)
  (import (chezscheme) (sbral))

  (define-structure (var id))
  (define-structure (substitution dict))

  (define substitution-empty (make-substitution sbral-empty))

  (define (walk v s)
    (if (var? v)
	(walk (sbral-ref s (var-id v)) v)
	v))

  (define (extend s x y)
    3
    )
  
  (define (unify x y s)
    (let ([x (walk x s)]
	  [y (walk y s)])
      (cond
       [(eq? x y) s]
       [(and (var? x) (var? y)) (assert #f)]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)])
      )
    ))
