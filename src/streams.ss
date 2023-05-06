;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification make-disj run-goal make-incomplete stream-step complete? bind)
  (import (chezscheme) (state) (failure) (runner) (goals))  

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))

  (define complete? pair?) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as a list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (mplus? s) (bind? s) (incomplete? s) (failure? s) (answer? s) (guarded? s) (complete? s)))

  (define-syntax stream-case
    (syntax-rules (else)
      ))
  
  (define (run-goal g s r)
    (assert (and (goal? g) (state? s) (runner? r)))
    (cond     
					;[(disj? g) (mplus (run-goal (disj-lhs g) s r) (run-goal (disj-rhs g) s r))]
     [(succeed? g) r]
     [(fresh? g) (g s r)]
     [(unification? g) (set-runner-stream r (unify s (unification-lhs g) (unification-rhs g)))]
     [(conj? g) (bind (conj-cdr g) (run-goal (conj-car g) s r))]
     [else (assert #f)]
     ))
  
  (define (mplus lhs rhs)
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(runner? lhs) (set-runner-stream lhs (mplus (runner-stream lhs) rhs))]
     [(answer? lhs) (cons lhs rhs)]
     [(answer? rhs) (cons rhs lhs)]
     [(make-mplus lhs rhs)]))

  (define (bind g r)
    (assert (and (goal? g) (runner? r)))
    (cond
     [(failure? (runner-stream r)) (set-runner-stream r failure)]
     [(state? (runner-stream r)) (run-goal g (runner-stream r) r)]
     [(incomplete? (runner-stream r)) (set-runner-stream r (make-incomplete g (runner-stream r)))]
     [else (assert #f)]))

  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(failure? s) (set-runner-stream r s)]
     [(state? (runner-stream r)) (stream-step failure r)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) r)]
     [(mplus? s) (mplus (stream-step (mplus-rhs s) r) (mplus-lhs s))]
     [else (assert #f)])))
