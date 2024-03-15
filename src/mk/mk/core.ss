(library (mk core) ; Provides the fundamental forms of the language.
  
  (export
   run run* run1 ; Run
   lazy-run lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-cdr* ; Lazy
   succeed fail == conde fresh exist matcho constraint conj disj noto =/= ; Goals
   __ ; Quantification
   answer-type answer-type answer-type/reified answer-type/state max-depth search-strategy search-strategy/interleaving search-strategy/dfs ; Parameters          
   )
  
  (import (chezscheme) (negation) (matcho) (search) (running) (variables) (goals)))
