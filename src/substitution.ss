(library (substitution)
  (export substitution-empty walk)
  (import (chezscheme) (sbral))

  (define-structure (var id))
  (define-structure (substitution dict))

  (define substitution-empty (make-substitution sbral-empty))

  (define (walk s v)
    (if (var? v)
	(walk (sbral-ref s (var-id v)) v)
	v)))
