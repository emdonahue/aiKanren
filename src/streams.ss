;;TODO replace (assert #f) with useful error messages
(library (streams)
  (export run-goal stream-step bind mplus run-dfs fire-dfs
	  store-constraint) ; TODO trim exports
  (import (chezscheme) (state) (failure) (goals) (package) (values) (constraint-store) (negation) (datatypes) (mini-substitution)) 

  (define (run-goal g s p)
    ;; Converts a goal into a stream. Primary interface for evaluating goals.
    (assert (and (goal? g) (state? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(fresh? g) (let-values ([(g s p) (g s p)]) ; TODO do freshes that dont change the state preserve low varid count?
		   (values (make-bind g s) p))]
     [(conj? g) (let-values ([(s p) (run-goal (conj-car g) s p)])
		  (bind (conj-cdr g) s p))]
     [(disj? g) (let*-values
		    ([(lhs p) (run-goal (disj-car g) s p)]
		     [(rhs p) (run-goal (disj-cdr g) s p)]) ; Although states are independent per branch, package is global and must be threaded through lhs and rhs.
		  (values (mplus lhs rhs) p))]
     [(and (noto? g)
	   (fresh? (noto-goal g))) (let-values ([(g s p) ((noto-goal g) s p)])
					       (values (make-bind (noto g) s) p))] 
     [else (values (fire-dfs g s) p)]))
  
  (define (mplus lhs rhs)
    ;; Interleaves two branches of the search
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (answers lhs rhs)] ; Float answers to the front of the tree
     [(answers? lhs) (answers (answers-car lhs) (mplus rhs (answers-cdr lhs)))]
     [(answer? rhs) (answers rhs lhs)]
     [(answers? rhs) (answers (answers-car rhs) (mplus lhs (answers-cdr rhs)))]
     [else (make-mplus lhs rhs)]))

  (define (bind g s p)
    ;; Applies g to all states in s.
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values failure p)]
     [(state? s) (run-goal g s p)]
     [(or (bind? s) (mplus? s)) (values (make-bind g s) p)]
     [(answers? s) (let*-values
			([(lhs p) (run-goal g (answers-car s) p)]
			 [(rhs p) (bind g (answers-cdr s) p)])
		      (values (mplus lhs rhs) p))]
     [else (assertion-violation 'bind "Unrecognized stream type" s)]))
  
  (define (stream-step s p)
    (assert (and (stream? s) (package? p))) ; -> goal? stream? package?
    (cond
     [(failure? s) (values s p)]
     [(state? s) (values s p)]
     [(bind? s)
      (let-values ([(s^ p) (stream-step (bind-stream s) p)])
	(bind (bind-goal s) s^ p))]
     [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) lhs) p))]
     [(answers? s) (values (answers-cdr s) p)]
     [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))

  ;; === CONSTRAINTS ===

  (define (==->vars g)
    ;;TODO can be subsumed by attr vars if normalize by vid to pick one
    (cond
     [(==? g) (list (==-lhs g))]
     [(conj? g) (map ==-lhs (conj-conjuncts g))]
     [else '()]))

  (define (=/=->var g)
    (assert (or (==? g) (conj? g)))
    (if (==? g) (list (==-lhs g))
	(=/=->var (conj-car g))))

  (define (may-unify g v)
    (cond
     [(==? g) (or (equal? (==-lhs g) v) (equal? (==-rhs g) v))]
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-cdr g) v))]
     [else #f]))

  (define (fire-dfs g s)
    (let-values ([(g s) (run-dfs g s succeed succeed 1)])
      (store-const2 s g))
    )

  (define (invert-disj ds)
    ;;TODO perhaps instead of a fully inverted disj constraint pair we can simply add a dummy proxy constraint that if looked up succeeds but raises the constraint waiting on the original vars
    (let ([rest (disj-cdr ds)])
      (if (disj? rest)
	  (normalized-disj* (disj-car rest) (disj-car ds) (disj-cdr rest))
	  (normalized-disj* rest (disj-car ds)))))
  
  (define (store-const2 s g)
    (cond
     [(conj? g) (store-const2 (store-const2 s (conj-car g)) (conj-cdr g))]
     [(disj? g) (store-constraint s g)]
     [else s]))
  
  (define (run-dfs g s conjs out mode)
    (assert (and (goal? g) (state? s) (goal? conjs) (number? mode)))
    (cond
     [(fail? g) (values fail failure)]
     [(succeed? g) (if (succeed? conjs) (values out s) (run-dfs conjs s succeed out 1))]
     [(==? g) (let-values ([(s g^) (unify s (==-lhs g) (==-rhs g))])
		(if (fail? g^) (values fail failure)
		    (run-dfs (conj* conjs (get-constraints s (==->vars g^)))
			     (remove-constraints s (==->vars g^))
			     succeed (normalized-conj* out g^) 1)))]
     [(and (noto? g) (==? (noto-goal g)))
      (let-values ([(s^ g) (unify s (==-lhs (noto-goal g)) (==-rhs (noto-goal g)))])
	(cond
	 [(succeed? g) (values fail failure)]
	 [(fail? g) (run-dfs conjs s succeed out 1)]
	 [(==? g)
	  (if (may-unify (get-constraints s (=/=->var g)) (car (=/=->var g)))
	      (run-dfs (conj* conjs (get-constraints s (==->vars g)))
		       (store-constraint (remove-constraints s (==->vars g)) (noto g))
		       succeed (normalized-conj* (noto g) out) 1)
	      (run-dfs conjs (store-constraint s (noto g)) succeed (normalized-conj* (noto g) out)  1))]
	 [else
	  (run-dfs conjs
		   (store-constraint
		    (store-constraint s (noto g))
		    (normalized-disj* (disj-cdr (noto g)) (disj-car (noto g))))
		   succeed
		   (normalized-conj* out (noto g)) 1)]))]
     [(disj? g) (let-values ([(g^ s^) (run-dfs (disj-car g) s conjs out 1)])
		  (cond
		   [(eq? g^ out) (values out s)]
		   [(fail? g^) (run-dfs (disj-cdr g) s conjs out mode)]
		   [else
		    (if (zero? mode) ;TODO can we special case some disj to only save on one disjunct?
			(values (normalized-disj* g^ (normalized-conj* (disj-cdr g) conjs)) s)
			(let-values ([(g2 s2) (run-dfs (disj-cdr g) s conjs out 0)])
			  (cond
			   [(fail? g2) (values (normalized-conj* g^ out) s^)]
			   [(succeed? g2) (values out s^)]
			   [else (values (normalized-disj* g^ g2) s)])))]))]
     [(conj? g) (run-dfs (conj-car g) s (normalized-conj* (conj-cdr g) conjs) out 1)]
     [(constraint? g) (run-dfs (constraint-goal g) s conjs out 1)]
     [(guardo? g) (let ([v (walk s (guardo-var g))])
		   (cond
		    [(var? v) (let ([g (guardo v (guardo-procedure g))])
				(values g (store-constraint s g)))]
		    [(pair? v) (run-dfs ((guardo-procedure g) (car v) (cdr v)) s conjs out 1)]
		    [else (values fail failure)]))]
     [(pconstraint? g) (assert #f) (values ((pconstraint-procedure g) s) s)]
     [else (assertion-violation 'run-dfs "Unrecognized constraint type" g)]))

  ;; constraint pulls all attributed vars into big conj. simplifies alone in state. recurse on that. if ever we pull only successes, just attribute

    (define (store-constraint s c)
    ;; Store simplified constraints into the constraint store.
    (assert (and (state-or-failure? s) (assert (or (guardo? c) (noto? c) (disj? c))))) ; -> state?
    (cond
     [(disj? c) (let* ([vars1 (get-attributed-vars c)]
		       [vars2 (filter (lambda (v) (not (memq v vars1))) (get-attributed-vars (disj-cdr c)))]
		       [c2 (invert-disj c)]
		       )
		  (fold-left
		   (lambda (s v)
		     (state-add-constraint s v c2))
		   (fold-left
		    (lambda (s v)
		      (state-add-constraint s v c)) s vars1) vars2)
		  )]
     [else ; All other constraints get assigned to their attributed variables.
      (fold-left
       (lambda (s v)
	 ;;(assert (eq? (walk s v) v)) ; TODO delete this assertion
	 (state-add-constraint s v c)) s (get-attributed-vars c))]))

  (define (get-attributed-vars g)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    ;; TODO optimize which constraint we pick to minimize free vars
    ;; TODO attributed vars should probably be deduplicated
    ;; TODO attributed vars should handle (constraint)'s
    (assert (goal? g)) ; Since conj constraints are run seperately, we only receive disj and primitives here.
    (cond
     [(succeed? g) '()]
     [(disj? g) (get-attributed-vars (disj-car g))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint
     [(conj? g) (apply append (map get-attributed-vars (conj-conjuncts g)))]
     [(noto? g) (get-attributed-vars (noto-goal g))]
     [(==? g) (assert (var? (==-lhs g))) (list (==-lhs g))]
     [(pconstraint? g) (pconstraint-vars g)]
     [(guardo? g) (list (guardo-var g))]
     [else (assertion-violation 'get-attributed-vars "Unrecognized constraint type" g)]))


  ) 
