;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification run-goal make-incomplete stream-step complete? bind)
  (import (chezscheme) (state) (failure) (runner) (goals) (package)) 

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))
  (define-values (complete complete? complete-car complete-cdr) (values cons pair? car cdr)) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as an improper list of answer?s, possibly with an improper stream tail.

  (define-syntax with-values ;TODO remove with-values
    (syntax-rules ()
      [(_ v ... proc) (call-with-values (lambda () (values v ...)) proc)]))
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (bind? s) (incomplete? s) (answer? s) (guarded? s) (complete? s)))

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p)))
    (cond     
     [(succeed? g) (values s p)]
     [(fail? g) (values failure p)]
     [(fresh? g) (g s p)]
     [(unification? g) (values (unify s (unification-lhs g) (unification-rhs g)) p)]
     [(conj? g) (let-values ([(s p) (run-goal (conj-car g) s p)])
		  (bind (conj-cdr g) s p))]
     [(disj? g) (run-disj g s p)]
     [else (assert #f)]))

  (define (run-disj g s p)
    ;;TODO streamline run-disj
    (let*-values
     ([(lhs p) (run-goal (disj-car g) s p)]
      [(rhs p) (run-goal (disj-cdr g) s p)])
     (values (mplus lhs rhs) p)))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs)))
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (complete lhs rhs)]
     [(complete? lhs) (complete (complete-car lhs) (mplus rhs (complete-cdr lhs)))]
     [else (assert #f)]))

  (define (bind g s p)
    (assert (and (goal? g) (stream? s) (package? p)))
    (cond
     [(failure? s) (values s p)]
     [(state? s) (run-goal g s p)]
     [(incomplete? s) (make-incomplete g s)]
     [(complete? s) (bind-complete g s p)]
     [else (assert #f)]))

  (define (bind-complete g s p)
    (assert (and (goal? g) (stream? s) (package? p)))
    (let-values ([(h p) (run-goal g (complete-car s) p)])
      (let-values ([(r p) (bind g (complete-cdr s) p)])
	(values (mplus h r) p)))
    )
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p)))
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values failure p)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) p)]
     [(mplus? s) (let-values ([(s p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) s) p))]
     [(complete? s) (values (complete-cdr s) p)]
     [else (assert #f)])))
