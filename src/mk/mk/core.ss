(library (mk core) ; Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.
  
  (export
   run run* run1 ; Run
   lazy-run lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-cdr* ; Lazy
   succeed fail == conde fresh exist matcho constraint conj disj noto =/= ; Goals
   __ ; Quantification
   reifier reifier/state reifier/query reifier/pretty-print reifier/constraints ; Reification
   max-depth search-strategy ; Search Parameters
   var var? var-id ; Variables
   state state? state-substitution state-varid state-attributes ; Streams
   state-priority priority-< beam-size ; Priority
   )
  
  (import (chezscheme) (mk core matcho) (mk core search) (mk core running) (mk core variables) (mk core goals) (mk core streams) (mk core reifier)))
