(library (state)
  (export make-state empty-state state? reify state-substitution)
  (import (chezscheme) (substitution))

  (define-structure (state substitution))
  (define empty-state (make-state substitution-empty))
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v) (reify s (walk (state-substitution s) v))]
     [else v]))
  
)
