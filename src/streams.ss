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
     [(=/=? g) (values (disunify s (=/=-lhs g) (=/=-rhs g)) p)]
     [(stale? g) (run-goal (noto (g)) s p)]
     [else (assert #f)]))

  (define (unify s x y)
    ;;TODO fold unify back into state
    ;;(printf "CONST: ~s~%ORIG: ~s~%OLDS: ~s~%NEWS: ~s~%~%" (extensions->goal extensions) (set-state-substitution s sub) stat (run-constraints2 (set-state-substitution s sub) (extensions->goal extensions)))
    ;;(printf "SUB ~s EXT ~s~%" sub extensions)
    (assert (state? s))
    (let-values ([(sub extensions) (state:unify s x y)])      
      (run-constraints2 (set-state-substitution s sub) extensions)))
  
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

  (define (run-constraints2 s g)
    (assert (and (state-or-failure? s) (goal? g)))

    (cond
     [(succeed? g) s]
     [(fail? g) failure]
     [(==? g) (run-constraint-goal
	       (constraint-goal
		(get-constraint (state-constraints s)
				(==-lhs g) empty-constraint))
	       s)] 
					;[(conj? g) ]
     [else (assert #f)])
    )

  (define (run-constraint-goal g s)
    (assert (and (state-or-failure? s) (goal? g)))
					;(printf "SIMPLIFIED: ~s~%" (simplify-constraint g s))
    (assert (goal? (simplify-constraint g s)))
    (apply-constraints s (simplify-constraint g s))
    #;
    (cond
     [(failure? s) s];TODO does failure ever get run as a constraint?
     [(succeed? g) s]
     [(fail? g) failure]
     #;
     [(==? g) (unify s (==-lhs g) (==-rhs g))]
     #;
     [(=/=? g) (disunify s (=/=-lhs g) (=/=-rhs g))]
     #;
     [(conj? g) (run-constraint-goal (conj-cdr g) (run-constraint-goal (conj-car g) s))]
     #;
     [(disj? g) (printf "DISJ: ~s~%" (run-constraint-goal (noto g) s)) (assert #f)]
     [else (assert #f)])
    )

  (define (simplify-constraint g s)
    (assert (and (goal? g) (state? s)))
    (cond
     [(or (succeed? g)) (fail? g) g]
     [(=/=? g) (noto (values-ref (state:unify s (=/=-lhs g) (=/=-rhs g)) 1))]
     [(conj? g) (normalized-conj (map (lambda (g) (simplify-constraint g s)) (conj-conjuncts g)))]
     [(disj? g) (normalized-disj (map (lambda (g) (simplify-constraint g s)) (disj-disjuncts g)))]
     ))

  (define (extensions->goal es)
    (if (not es) fail (conj (map (lambda (e) (== (car e) (cdr e))) es))))
  
  (define (disunify s x y)
    (assert (state? s))			; -> state-or-failure?
    ;(run-constraint-goal (noto (== x y)) s)
    (run-constraint-goal (noto (== x y)) s))

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
	    s (merge-constraint (state-constraints s) v c))) s (get-attributed-vars c))]))


    )
