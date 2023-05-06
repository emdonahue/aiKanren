;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification run-goal make-incomplete stream-step complete? bind)
  (import (chezscheme) (state) (failure) (runner) (goals) (package)) 

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))
  (define-values (complete complete? complete-car complete-cdr) (values cons pair? car cdr)) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as an improper list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (mplus? s) (bind? s) (incomplete? s) (failure? s) (answer? s) (guarded? s) (complete? s)))

  (define (run-goal g s r)
    (assert (and (goal? g) (state? s) (runner? r)))
    (cond     
     [(succeed? g) (set-runner-stream r s)]
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
      (set-runner-stream rhs (mplus (runner-stream lhs) (runner-stream rhs)))))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs)))
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (complete lhs rhs)]
     [(complete? lhs) (complete (complete-car lhs) (mplus rhs (complete-cdr lhs)))]
     [else (assert #f)]))

  (define (bind r g)
    (assert (and (goal? g) (runner? r)))
    (cond
     [(failure? (runner-stream r)) (set-runner-stream r failure)]
     [(state? (runner-stream r)) (run-goal g (runner-stream r) r)]
     [(incomplete? (runner-stream r)) (set-runner-stream r (make-incomplete g (runner-stream r)))]
     [(complete? (runner-stream r)) (bind-complete g r)]
     [else (assert #f)]))

    (define (bind-complete g r)
;    (assert (and (goal? g) (package? p) (complete? (runner-stream r))))
    (let ([h (run-goal g (complete-car (runner-stream r)) r)])
      (let ([r (bind (set-runner-stream r (complete-cdr (runner-stream r))) g)])
	(set-runner-stream h (mplus (runner-stream h) (runner-stream r)))))
    )
  
  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(failure? s) (set-runner-stream r s)]
     [(state? (runner-stream r)) (stream-step failure r)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) r)]
     [(mplus? s) (let ([r (stream-step (mplus-rhs s) r)])
		   (set-runner-stream r (mplus (runner-stream r) (mplus-lhs s))))]
     [(complete? s) (set-runner-stream r (complete-cdr (runner-stream r)))]
     [else (assert #f)])))
