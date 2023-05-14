;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus run-stream-constraint run-stream-constraint)
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes)) 

  (define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(succeed? g) (values succeed s p)]
     [(fail? g) (values fail failure p)]
     [(==? g) (let-values ([(s g) (simplify-unification s (==-lhs g) (==-rhs g))])
		(values g s p))]
     [(fresh? g) (let-values ([(g s p) (g s p)])
		   (values g (make-incomplete g s) p))]
     [(conj? g) (let-values ([(xxx s p) (run-goal (conj-car g) s p)])
		  (bind (conj-cdr g) s p))]
     [(disj? g) (let*-values
		    ([(lhg lhs p) (run-goal (disj-car g) s p)]
		     [(rhg rhs p) (run-goal (disj-cdr g) s p)])
		  (values (disj* lhg rhg) (mplus lhs rhs) p))]
     [(and (noto? g) (fresh? (noto-goal g))) (let-values ([(g s p) (g s p)])
					       (run-goal (noto g) s p))]
     [(and (noto? g) (not (fresh? (noto-goal g))))
      (let*-values ([(g s^ p) (run-goal (noto-goal g) s p)]
		    [(g) (noto g)])
	(values g (store-constraint s g) p))]
     [else (let-values ([(s p)
			 (cond     
			  
			  
			  
			  
			  
			  [(=/=? g) (values (run-constraint s (noto (== (=/=-lhs g) (=/=-rhs g)))) p)]
			  
			  [(constraint? g) (values (run-constraint s (constraint-goal g)) p)]
			  [else (assert #f) (values 1 2)])]) (values 'run-goal-goal s p))]))

  #;(define (run-goal g s p)
    (assert (and (goal? g) (state? s) (package? p))) ; ->stream? package?
    (cond     
     [(succeed? g) (values succeed s p)]
     [(fail? g) (values fail failure p)]
     [(fresh? g)
      (let-values ([(g s p) (g s p)])
	(values g (make-incomplete g s) p))]
     [(==? g)
      (let-values ([(s g) (unify s (==-lhs g) (==-rhs g))])
	(values g s p))]
     [(conj? g)
      (let-values ([(g0 s p) (run-goal (conj-car g) s p)]
		   [(g s p) (bind (conj-cdr g) s p)])
	(values (normalized-conj* g0 g) s p))]
     [(disj? g)
      (let*-values
	  ([(lhg lhs p) (run-goal (disj-car g) s p)]
	   [(rhg rhs p) (run-goal (disj-cdr g) s p)])
	(values (normalized-disj* lhg rhg) (mplus lhs rhs) p))]
     [(=/=? g) (values g (run-constraint s (noto (== (=/=-lhs g) (=/=-rhs g)))) p)]
     [(noto? g) (run-goal (noto (g s p)) s p)]
     [(constraint? g) (values g (run-constraint s (constraint-goal g)) p)]
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
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values fail failure p)]
     [(state? s) (let-values ([(g^ s p) (run-goal g s p)])
		   (values (normalized-conj* g g^) s p))]
     [(incomplete? s) (values 'bind-incomplete (make-incomplete g s) p)]
     [(complete? s)
      (let*-values
	  ([(xxx h p) (run-goal g (complete-car s) p)]
	   [(xxx r p) (bind g (complete-cdr s) p)])
	(values 'bind-complete (mplus h r) p))]
     [else (assert #f)]))

  #;
  (define (run-stream-constraint s g)
    (assert (and (state-or-failure? s) (goal? g))) ; -> state? goal?
    (cond
     [(or (failure? s) (fail? g)) (values failure g)]
     [(succeed? g) (values s g)]
     [(==? g) (simplify-unification s (==-lhs g) (==-rhs g))]
     [(=/=? g) (values s (noto (values-ref (simplify-unification s (=/=-lhs g) (=/=-rhs g)) 1)))]
     ;;[(fresh? g) (run-stream-constraint s (first-value (g s empty-package)))]
     [(conj? g)
      (let-values ([(s g) (run-stream-constraint s (conj-car g))]
		   [(xxx b gs) (bind (conj-cdr g) s empty-package)])
	(values  (normalized-conj* g )))]
     ;;[(conj? g) (run-conj s (conj-conjuncts g) succeed)]
     ;;[(disj? g) (run-disj s (disj-disjuncts g) fail failure)]
     [(disj? g)
      (let*-values
	  ([(lhs lhg) (run-stream-constraint s (disj-car g))]
	   [(rhs rhg) (run-stream-constraint s (disj-cdr g))])
	(values (mplus lhs rhs) (normalized-disj* lhg rhg)))]
     [(constraint? g) (run-stream-constraint s (constraint-goal g))]
     [else (assert #f)]))

  (define (stream-constraint-step s)
    (assert (stream? s))
    (cond
     [(failure? s) s]
     
     [else (assert #f)] ))

  (define (run-stream-constraint g s0)
    (let-values ([(g s p) (run-goal g s0 empty-package)])
      (printf "CONSTRAINT: ~s~%STATE: ~s~%" g s)
      (cond
       [(fail? g) failure]
       [(succeed? g) s0]
       [(state? s) s]
       [(disj? g) (store-constraint s0 g)] ; TODO increase the var-id counter
       [else (assert #f)])))
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p))) ; ->stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values failure p)]
     [(incomplete? s)
      (let-values ([(g s p) (run-goal (incomplete-goal s) (incomplete-state s) p)])
	(values s p))]
     [(mplus? s) (let-values ([(s p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) s) p))]
     [(complete? s) (values (complete-cdr s) p)]
     [else (assert #f)]))) 
