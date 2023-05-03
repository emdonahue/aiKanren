(library (state)
  (export make-state empty-state state?)
  (import (chezscheme) (substitution))

  (define-structure (state substitution))
  (define empty-state (make-state substitution-empty))

  
)
