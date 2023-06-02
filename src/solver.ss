(library (solver)
  (export run-constraint)
  (import (chezscheme) (state) (negation) (datatypes))

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint. 
    (let-values ([(g s) (run-dfs g s succeed succeed 1)])
      (store-const2 s g)))
  
  (define (may-unify g v)
    (cond
     [(==? g) (or (equal? (==-lhs g) v) (equal? (==-rhs g) v))]
     [(conj? g) (or (may-unify (conj-car g) v) (may-unify (conj-cdr g) v))]
     [(disj? g) (or (may-unify (disj-car g) v) (may-unify (disj-cdr g) v))]
     [else #f]))
  
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
     [(==? g) (let-values ([(g^ s) (unify s (==-lhs g) (==-rhs g))])
		(if (fail? g^) (values fail failure)
		    (run-dfs (conj* conjs (get-constraints s (attributed-vars g^)))
			     (remove-constraints s (attributed-vars g^))
			     succeed (normalized-conj* out g^) 1)))]
     [(and (noto? g) (==? (noto-goal g)))
      (let-values ([(g s^) (unify s (==-lhs (noto-goal g)) (==-rhs (noto-goal g)))])
	(cond
	 [(succeed? g) (values fail failure)]
	 [(fail? g) (run-dfs conjs s succeed out 1)]
	 [(==? g)
	  (if (may-unify (get-constraints s (attributed-vars g)) (car (attributed-vars g)))
	      (run-dfs (conj* conjs (get-constraints s (attributed-vars g)))
		       (store-constraint (remove-constraints s (attributed-vars g)) (noto g))
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
    (assert (and (state? s) (assert (or (guardo? c) (noto? c) (disj? c))))) ; -> state?
    (cond
     [(disj? c) (let* ([vars1 (attributed-vars c)]
		       [vars2 (remp (lambda (v) (memq v vars1)) (attributed-vars (disj-cdr c)))]) ;TODO be more specific about how many disjuncts we need attr vars from
		  (state-add-constraint (state-add-constraint s (invert-disj c) vars2) c vars1))]
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s c (attributed-vars c))]))

  (define (invert-disj ds)
    ;;TODO perhaps instead of a fully inverted disj constraint pair we can simply add a dummy proxy constraint that if looked up succeeds but raises the constraint waiting on the original vars
    (let ([rest (disj-cdr ds)])
      (if (disj? rest)
	  (normalized-disj* (disj-car rest) (disj-car ds) (disj-cdr rest))
	  (normalized-disj* rest (disj-car ds)))))
  
  (define (attributed-vars g)
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (fold-right (lambda (v vs) (if (memq v vs) vs (cons v vs))) '() (non-unique-attributed-vars g)))
  
  (define (non-unique-attributed-vars g)    
    ;; TODO optimize which constraint we pick to minimize free vars
    (assert (goal? g))
    (cond
     [(succeed? g) '()]
     [(disj? g) (attributed-vars (disj-car g))] ; Attributed vars are all free vars, except in the case of disj, in which case it is the free vars of any one constraint TODO if we are checking 2 disjuncts, do we need both attr vars?
     [(conj? g) (apply append (map attributed-vars (conj-conjuncts g)))]
     [(noto? g) (attributed-vars (noto-goal g))]
     [(==? g) (assert (var? (==-lhs g))) (list (==-lhs g))]
     [(pconstraint? g) (pconstraint-vars g)]
     [(guardo? g) (list (guardo-var g))]
     [(constraint? g) (attributed-vars (constraint-goal g))]
     [else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)]))
  
)
