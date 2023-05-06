;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification run-goal make-incomplete stream-step complete? bind)
  (import (chezscheme) (state) (failure) (runner) (goals))  

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))

  (define complete cons) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as an improper list of answer?s, possibly with an improper stream tail.
  (define complete? pair?)
  (define complete-car car)
  (define complete-cdr cdr)
  
  (define (stream? s)
    (or (mplus? s) (bind? s) (incomplete? s) (failure? s) (answer? s) (guarded? s) (complete? s)))

  ;;TODO consider simplifying bind/mplus with stream-case
  #;
  (define-syntax stream-case
    (syntax-rules (else)
      [(_ in-runner in-stream [else out-runner ...])
       (begin out-runner ...)]
      [(_ in-runner in-stream [type? out-runner ...])
       (if (type? (in-stream)))]
      [(_ in-runner in-stream [type? out-stream] ...)
       (if (type? (runner-stream in-runner))

	   )
       3]))
  
  (define (run-goal g s r)
    (assert (and (goal? g) (state? s) (runner? r)))
    (cond     
					;[(disj? g) (mplus (run-goal (disj-lhs g) s r) (run-goal (disj-rhs g) s r))]
     [(succeed? g) r]
     [(fail? g) (set-runner-stream r failure)]
     [(fresh? g) (g s r)]
     [(unification? g) (set-runner-stream r (unify s (unification-lhs g) (unification-rhs g)))]
     [(conj? g) (bind (run-goal (conj-car g) s r) (conj-cdr g))]
     [(disj? g) (run-disj g s r)]
     [else (assert #f)]
     ))

  (define (run-disj g s r)
    ;;TODO streamline run-disj
    (let* ([lhs (run-goal (disj-car g) s r)]
	   [rhs (run-goal (disj-cdr g) s lhs)])
      (mplus (set-runner-stream rhs (runner-stream lhs)) rhs)))

  (define (bind-complete r g)
    (assert (and (goal? g) (runner? r) (complete? (runner-stream r))))
    (let ([h (run-goal g (complete-car (runner-stream r)) r)])
      (mplus h (bind (set-runner-stream r (complete-cdr (runner-stream r))) g)))
    )
  
  (define (mplus lhs rhs)
    ;; lhs contains the most recent table, so that runner should be used regardless of which stream is returned.
    (assert (and (runner? lhs) (runner? rhs)))
    (cond
     [(failure? (runner-stream lhs)) (set-runner-stream lhs (runner-stream rhs))]
     [(failure? (runner-stream rhs)) lhs]
     [(answer? (runner-stream lhs))
      (set-runner-stream lhs (complete (runner-stream lhs) (runner-stream rhs)))]
     [(complete? (runner-stream lhs))
      (set-runner-stream lhs (complete (complete-car (runner-stream lhs)) (runner-stream (mplus rhs (set-runner-stream lhs (complete-cdr (runner-stream lhs)))))))]
     ;;[(runner? lhs) (set-runner-stream lhs (mplus (runner-stream lhs) rhs))]
     ;;[(answer? lhs) (cons lhs rhs)]
     ;;[(answer? rhs) (cons rhs lhs)]
     [else (assert #f)]))

  (define (bind r g)
    (assert (and (goal? g) (runner? r)))
    (cond
     [(failure? (runner-stream r)) (set-runner-stream r failure)]
     [(state? (runner-stream r)) (run-goal g (runner-stream r) r)]
     [(incomplete? (runner-stream r)) (set-runner-stream r (make-incomplete g (runner-stream r)))]
     [(complete? (runner-stream r)) (bind-complete r g)]
     [else (assert #f)]))

  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(failure? s) (set-runner-stream r s)]
     [(state? (runner-stream r)) (stream-step failure r)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) r)]
     [(mplus? s) (mplus (stream-step (mplus-rhs s) r) (mplus-lhs s))]
     [(complete? s) (set-runner-stream r (complete-cdr ))]
     [else (assert #f)])))
