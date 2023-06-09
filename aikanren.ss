;; TODO can we get guarded goal functionality by an == constraint and a schedule that when run unifies the guarded variables thereby triggering the unification?
;; TODO do == and =/= automatically simplify when merged because we run constraints on the state not the substitution when reducing?
;; TODO bool is just true or false. does this automatically gel with =/= of the other one?
;; TODO we can get finite domain like ability to actually generate the answers by popping the constraint and treating it as a goal
;;TODO test whether optimize level works for whole library
(library (aikanren)
  (export
   run1 run run* ;Run Interface
   
   succeed == conde fresh ;Goals
   )
  (import (chezscheme) (ui))


)
