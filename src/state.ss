(library (state)
  (export make-state empty-state state? reify state-substitution)
  (import (chezscheme) (substitution))

  (define-structure (state substitution))
  (define empty-state (make-state substitution-empty))
  (define (reify s v)
    (if (pair? v)
	(cons (reify s (car v)) (reify s (cdr v)))
	(reify s (walk (state-substitution s) v))))
  
)
