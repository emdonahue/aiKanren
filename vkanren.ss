;; can we get guarded goal functionality by an == constraint and a schedule that when run unifies the guarded variables thereby triggering the unification?
;; do == and =/= automatically simplify when merged because we run constraints on the state not the substitution when reducing?
;; bool is just true or false. does this automatically gel with =/= of the other one?
;; we can get finite domain like ability to actually generate the answers by popping the constraint and treating it as a goal
(library (vkanren)
  (export)
  (import (chezscheme) (sbral) (substitution))


  (define x 1))
