(library (mk core) ; Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.
; Note too that, in addition to the goal constructors listed here, any procedure can be used transparently as a goal (but not a constraint). The procedure must accept 3 arguments: the state containing the substitution and constraints, the package containing search-wide global data such as table data, and a goal representing the future goals in the current search. It must return 4 values: a goal that will be run immediately after return (or just the trivial **succeed** goal), the new state, the new package, and the new goal representing the future of the search.
  
  (export
   run run* run1 ; Run
   lazy-run lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-cdr* ; Lazy
   succeed fail == conde fresh exist matcho constraint conj disj noto =/= ; Goals
   __ ; Quantification
   answer-type max-depth search-strategy ; Parameters          
   )
  
  (import (chezscheme) (negation) (matcho) (search) (running) (variables) (goals)))
