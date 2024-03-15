(library (mk core)
  
  (export run run* run1 ; Run
          lazy-run lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-cdr* ; Lazy-Run
          constraint succeed fail == conde fresh exist matcho conj disj noto =/= ; Goals
          __ ; Quantification
          search-strategy max-depth answer-type ; Parameters
          search-strategy/interleaving search-strategy/dfs answer-type answer-type/reified answer-type/state ; Parameter-Values)   
          )
  
  (import (chezscheme) (negation) (matcho) (search) (running) (variables) (goals)))
