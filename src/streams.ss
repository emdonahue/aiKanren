;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus run-stream-constraint)
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes)) 

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
     [(=/=? g) (values (run-constraint s (noto (== (=/=-lhs g) (=/=-rhs g)))) p)]
     [(noto? g) (run-goal (noto (g)) s p)]
     [(constraint? g) (values (run-constraint s (constraint-goal g)) p)]
     [else (assert #f)]))
  
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

  (define (run-stream-constraint s g)
    (assert (and (state-or-failure? s) (goal? g))) ; -> state? goal?
    (cond
     [(or (failure? s) (fail? g)) (values failure g)]
     [(succeed? g) (values s g)]
     [(==? g) (simplify-unification s (==-lhs g) (==-rhs g))]
     [(=/=? g) (values s (noto (values-ref (simplify-unification s (=/=-lhs g) (=/=-rhs g)) 1)))]
     ;;[(fresh? g) (run-stream-constraint s (first-value (g s empty-package)))]
     [(conj? g)
      (let-values ([(s p) (run-goal (conj-car g) s empty-package)])
	(bind (conj-cdr g) s p))]
     ;;[(conj? g) (run-conj s (conj-conjuncts g) succeed)]
     ;;[(disj? g) (run-disj s (disj-disjuncts g) fail failure)]
     [(constraint? g) (run-stream-constraint s (constraint-goal g))]
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
