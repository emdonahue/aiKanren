;; TODO can we get guarded goal functionality by an == constraint and a schedule that when run unifies the guarded variables thereby triggering the unification?
;; TODO do == and =/= automatically simplify when merged because we run constraints on the state not the substitution when reducing?
;; TODO bool is just true or false. does this automatically gel with =/= of the other one?
;; TODO we can get finite domain like ability to actually generate the answers by popping the constraint and treating it as a goal
;;TODO test whether optimize level works for whole library
;; TODO unify indentation to tabs. remove spaces
(library (mk)
  (export
   run run* run1 ; Run
   lazy-run lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-cdr* ; Lazy-Run
   constraint succeed fail == conde fresh exist matcho ; Goals
   conj disj noto =/=
   booleano presento absento listo finite-domain ==> typeo symbolo numbero pairo ; Constraints
   membero appendo assoco asspo for-eacho filtero ; List
   __ ; Quantification
   printfo displayo noopo var ; Debugging
   trace-goal trace-run trace-run* trace-conde prove trace-goals ; Tracing
   search-strategy max-depth answer-type ; Parameters
   search-strategy/interleaving search-strategy/dfs answer-type answer-type/reified answer-type/state ; Parameter-Values
   )
  (import (chezscheme) (negation) (matcho) (debugging) (search) (running) (variables) (goals) (mk tracing) (mk listo) (mk constraints)))
