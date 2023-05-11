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
    (let-values ([(sub extensions) (state:unify s x y)])      
      (check-constraints (set-state-substitution s sub) extensions)))
  
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
     [else (assert #f)]))


  ;; === DISEQUALITY ===

  (define (check-constraints s g)
    ;; Runs after unification to propagate new extensions through the constraint store
    (assert (and (state-or-failure? s) (goal? g)))
    (cond
     [(or (failure? s) (fail? g)) failure] ; State has failed
     [(succeed? g) s] ; State has succeeded without modification     
     [(==? g) (run-constraint
	       (get-constraint (state-constraints s)
			       (==-lhs g)) s)] ; State has updated a single variable
     [(conj? g) (check-constraints (check-constraints s (conj-car g)) (conj-cdr g))]
     [else (assert #f)]))

  (define (run-constraint g s)
    (assert (and (state-or-failure? s) (goal? g)))
    (apply-constraints s (simplify-constraint g s)))

  (define (simplify-constraint g s)
    ;; Reduce the constraint to simplest form given the current substitution
    (assert (and (goal? g) (state? s)))
    (cond
     [(or (succeed? g)) (fail? g) g]
     [(=/=? g) (noto (values-ref (state:unify s (=/=-lhs g) (=/=-rhs g)) 1))]
     [(conj? g) (normalized-conj (map (lambda (g) (simplify-constraint g s)) (conj-conjuncts g)))]
     [(disj? g) (normalized-disj (map (lambda (g) (simplify-constraint g s)) (disj-disjuncts g)))]))

    (define (get-attributed-vars c)
      (assert (not (conj? c)))
      (if (disj? c) (get-attributed-vars (disj-car c)) (filter var? (vector->list c))))

    (define (apply-constraints s c)
      (assert (and (state? s) (goal? c)))
      (cond
       [(succeed? c) s]
       [(fail? c) failure]
       [(conj? c) (fold-left apply-constraints s (disj-disjuncts c))]
       [else 
	(fold-left
	 (lambda (s v)
	   (set-state-constraints
	    s (add-constraint (state-constraints s) v c))) s (get-attributed-vars c))])))
