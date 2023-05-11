;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus)
  (import (chezscheme) (except (state) unify) (prefix (only (state) unify) state:) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes)) 

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; ->stream? package?
    (cond     
     [(succeed? g) (values s p)]
     [(fail? g) (values failure p)]
     [(fresh? g) (values (make-incomplete (g) s) p)]
     [(==? g) (values (unify s (==-lhs g) (==-rhs g)) p)]
     [(conj? g)
      (let-values ([(s p) (run-goal (conj-car g) s p)])
	(bind (conj-cdr g) s p))]
     [(disj? g)
      (let*-values
	  ([(lhs p) (run-goal (disj-car g) s p)]
	   [(rhs p) (run-goal (disj-cdr g) s p)])
	(values (mplus lhs rhs) p))]
     ;(run-constraint (noto (== x y)) s)
     [(=/=? g) (values (run-constraint (noto (== (=/=-lhs g) (=/=-rhs g))) s) p)]
     [(stale? g) (run-goal (noto (g)) s p)]
     [else (assert #f)]))

  (define (unify s x y)
    ;;TODO fold unify back into state
    (assert (state? s))
    (state:unify s x y))
  
  (define (mplus lhs rhs)
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (complete lhs rhs)]
     [(complete? lhs) (complete (complete-car lhs) (mplus rhs (complete-cdr lhs)))]
     [else (assert #f)]))

  (define (bind g s p)
    (assert (and (goal? g) (stream? s) (package? p))) ; ->stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (run-goal g s p)]
     [(incomplete? s) (make-incomplete g s)]
     [(complete? s)
      (let*-values
	  ([(h p) (run-goal g (complete-car s) p)]
	   [(r p) (bind g (complete-cdr s) p)])
	(values (mplus h r) p))]
     [else (assert #f)]))
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p))) ; ->stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values failure p)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) p)]
     [(mplus? s) (let-values ([(s p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) s) p))]
     [(complete? s) (values (complete-cdr s) p)]
     [else (assert #f)]))) 
