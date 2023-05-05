;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification make-disj run-goal make-incomplete stream-step complete?)
  (import (chezscheme) (state) (failure) (runner))  

  ;; === GOALS ===

  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))

  (define (goal? g)
    (or (procedure? g) (unification? g) (conj? g) (disj? g)))

  (define (run-goal g s r)
    (assert (and (goal? g) (stream? s) (runner? r)))
    (cond     
     ;[(disj? g) (mplus (run-goal (disj-lhs g) s r) (run-goal (disj-rhs g) s r))]
     [(procedure? g) (g s r)]
     [(unification? g) (set-runner-stream r (unify s (unification-lhs g) (unification-rhs g)))]
     [else (assert #f)]
     ))

  ;; === STREAMS ===

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))

  (define complete? pair?) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as a list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (mplus? s) (bind? s) (incomplete? s) (failure? s) (answer? s) (guarded? s) (complete? s)))
  
  (define (mplus lhs rhs)
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(runner? lhs) (set-runner-stream lhs (mplus (runner-stream lhs) rhs))]
     [(answer? lhs) (cons lhs rhs)]
     [(answer? rhs) (cons rhs lhs)]
     [(make-mplus lhs rhs)]))

    #;
  (define (bind g s)
    (cond
     [(null? s) '()]
     [(state? s) (run-goal g s)]
     [(mplus? s) (make-bind g s)]
     [else (assert #f)]))

  #;
  (define-syntax bind*
    (syntax-rules ()
      [(_ s) s]
      [(_ s g0 g ...) (bind* (bind g0 s) g ...)]))

  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(failure? s) (set-runner-stream r s)]
     [(state? (runner-stream r)) (stream-step failure r)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) r)]
     [(mplus? s) (mplus (stream-step (mplus-rhs s) r) (mplus-lhs s))]
     [else (assert #f)])))
