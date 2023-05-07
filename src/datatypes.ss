;TODO delete datatypes.ss
(library (datatypes)
  (export make-state empty-state state? empty-substitution set-state-substitution)
  (import (chezscheme))

  ;; === SUBSTITUTION ===
  
  (define-structure (substitution dict))
  (define empty-substitution (make-substitution sbral-empty))

  ;; === STATE ===
  
  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution #f '() #f 0))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) failure)))
