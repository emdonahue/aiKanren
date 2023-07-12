;;TODO replace assert #f with useful error messages
(library (goals)
  (export run-goal stream-step) ; TODO trim exports
  (import (chezscheme) (state) (failure) (package) (store) (negation) (datatypes) (solver) (utils)) 

  (org-define (run-goal g s p)
    ;; Converts a goal into a stream. Primary interface for evaluating goals.
    (assert (and (goal? g) (state-or-failure? s) (package? p))) ; -> stream? package?
    (exclusive-cond
     [(conj? g) (let-values ([(s p) (run-goal (conj-car g) s p)])
	       (bind (conj-cdr g) s p))]
     [(fresh? g) (let-values ([(g s^ p) (g s p)]) ; TODO do freshes that dont change the state preserve low varid count?
		   (suspend g s^ p s))]
     [(exist? g) (call-with-values ; TODO do freshes that dont change the state preserve low varid count?
		     (lambda () ((exist-procedure g) s p))
		   run-goal)]
     [(conde? g) (let*-values
		 ([(lhs p) (run-goal (conde-lhs g) s p)]
		  [(rhs p) (run-goal (conde-rhs g) s p)]) ; Although states are independent per branch, package is global and must be threaded through lhs and rhs.
		 (values (mplus lhs rhs) p))]
     [(matcho? g) (let-values ([(structurally-recursive? g s^ p) (expand-matcho g s p)]) ;TODO check whether structural recursion check is needed anymore for matcho or if single state return is enough
		    (if structurally-recursive? ; If any vars are non-free, there is structurally recursive information to exploit, 
			(run-goal g s^ p) ; so continue running aggressively on this branch.
			(suspend g s^ p s)))] ; Otherwise suspend like a normal fresh.
     [else (values (run-constraint g s) p)]))
  
  (define (mplus lhs rhs)
    ;; Interleaves two branches of the search
    (assert (and (stream? lhs) (stream? rhs))) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (make-answers lhs rhs)] ; Float answers to the front of the tree
     [(answers? lhs) (make-answers (answers-car lhs) (mplus rhs (answers-cdr lhs)))]
     [(answer? rhs) (make-answers rhs lhs)]
     [(answers? rhs) (make-answers (answers-car rhs) (mplus lhs (answers-cdr rhs)))]
     [else (make-mplus lhs rhs)]))

  (define (bind g s p)
    ;; Applies g to all states in s.
    (assert (and (goal? g) (stream? s) (package? p))) ; -> goal? stream? package?
    (exclusive-cond
     [(failure? s) (values failure p)]
     [(state? s) (run-goal g s p)]
     [(or (bind? s) (mplus? s)) (values (make-bind g s) p)]
     [(answers? s) (let*-values
		       ([(lhs p) (run-goal g (answers-car s) p)]
			[(rhs p) (bind g (answers-cdr s) p)])
		     (values (mplus lhs rhs) p))]
     [else (assertion-violation 'bind "Unrecognized stream type" s)]))

  (define (suspend g s^ p s)
    ;;TODO make trivially succeeding freshes return just s to discard unneeded fresh ids
    (cert (goal? g) (state-or-failure? s^) (package? p) (state? s))
    (exclusive-cond
     [(fail? g) (values failure p)]
     [(succeed? g) (values s^ p)] ; Trivial successes can throw away any var ids reserved for fresh vars, as the substitution will never see them.
     [else (values (make-bind g s^) p)]))
  
  (define (stream-step s p) ;TODO experiment with mutation-based mplus branch swap combined with answer return in one call
    (assert (and (stream? s) (package? p))) ; -> goal? stream? package?
    (exclusive-cond
     [(failure? s) (values s p)]
     [(state? s) (values s p)]
     [(bind? s) (let-values ([(s^ p) (stream-step (bind-stream s) p)])
		  (bind (bind-goal s) s^ p))]
     [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
		   (values (mplus (mplus-rhs s) lhs) p))]
     [(answers? s) (values (answers-cdr s) p)]
     [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))) 
