;;TODO replace assert #f with useful error messages
(library (goals)
  (export run-goal run-goal-dfs stream-step)
  (import (chezscheme) (state) (failure) (package) (store) (negation) (datatypes) (solver) (utils) (debugging)) 

  ;; === INTERLEAVING INTERPRETER ===
  
  (define (run-goal g s p) ;TODO define a secondary run goal that runs children of conde and only that one should suspend fresh because it represents having to make a choice instead of pursuing a goal linearly into its depths
	      ;;TODO if we convert interleaving to cps, we can use the goal structure to store tracing info and trace the interleaving search without special affordances
    ;; Converts a goal into a stream. Primary interface for evaluating goals.
	      (cert (goal? g) (state-or-failure? s) (package? p)) ; -> stream? package?
;	      (org-display (print-substitution s) (print-reification s))
    (exclusive-cond
     [(conj? g) (let-values ([(s p) (run-goal (conj-car g) s p)])
	       (bind (conj-cdr g) s p))]
     [(fresh? g) (let-values ([(g s^ p) (g s p)]) ; TODO do freshes that dont change the state preserve low varid count?
		   (suspend g s^ p s))] ;TODO separate suspended into its own constraint and treat procedures as ad hoc goals to be run immediately. ad hoc goals that already guarantee normal form can simply return succeed and the new state/package
     [(exist? g) (call-with-values ; TODO do freshes that dont change the state preserve low varid count?
		     (lambda () ((exist-procedure g) s p))
		   run-goal)]
     [(conde? g) (let*-values
		 ([(lhs p) (run-goal (conde-lhs g) s p)]
		  [(rhs p) (run-goal (conde-rhs g) s p)]) ; Although states are independent per branch, package is global and must be threaded through lhs and rhs.
		 (values (mplus lhs rhs) p))]
     [(matcho? g) (let-values ([(structurally-recursive? g s^ p) (expand-matcho g s p)]) ;TODO check whether structural recursion check is needed anymore for matcho or if single state return is enough
		    (if structurally-recursive?
			(suspend g s^ p s);(run-goal g s^ p)
			(suspend g s^ p s))
		    #;
		    (if (and #f structurally-recursive?) ; If any vars are non-free, there is structurally recursive information to exploit, 
			(run-goal g s^ p) ; so continue running aggressively on this branch.
		    (suspend g s^ p s)))] ; Otherwise suspend like a normal fresh.
     [(trace-goal? g) (run-goal (trace-goal-goal g) s p)] ;TODO move trace-goal to a procedure that checks for tracing params and only returns trace goal objects if tracing, otherwise noop and can remove from non tracing interpreters
     ;; TODO use the ==s from constraints to simplify continuations in normal goal interpreter
     [else (values (run-constraint g s) p)]))
  
  (define (mplus lhs rhs)
    ;; Interleaves two branches of the search
    (cert (stream? lhs) (stream? rhs)) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(answer? lhs) (make-answers lhs rhs)] ; Float answers to the front of the tree
     [(answers? lhs) (make-answers (answers-car lhs) (mplus rhs (answers-cdr lhs)))]
     [(answer? rhs) (make-answers rhs lhs)]
     [(answers? rhs) (make-answers (answers-car rhs) (mplus lhs (answers-cdr rhs)))]
     [else (make-mplus lhs rhs)]))

  (define (bind g s p) ;TODO consider making bind cps
    ;; Applies g to all states in s.
    (cert (goal? g) (stream? s) (package? p)) ; -> goal? stream? package?
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
    (cert (goal? g) (state-or-failure? s^) (package? p) (state? s))
    (exclusive-cond
     [(fail? g) (values failure p)]
     [(succeed? g) (values s p)] ; Trivial successes can throw away any var ids reserved for fresh vars, as the substitution will never see them.
     [else (values (make-bind g s^) p)]))

  ;; === DEPTH FIRST INTERPRETER ===

  (define (run-goal-dfs g s p n depth answers ctn) ;TODO consider analyzing goals in goal interpreter and running dfs if not recursive or only tail recursive. may require converting everything to cps. maybe use syntax analysis and a special conj type that marks its contents for dfs, where fresh bounces back to normal goal interpreter. it may not make a difference as outside of fresh a cps goal interpreter might be functionally depth first outside of trampolining
    ;;TODO if we put run-goal-dfs in a parameter the tracing system will have a callback fn and we can trace without modifying the dfs
    (cond ; TODO consider manipulating ctn order in dfs to get different searches, such as depth-ordered search using a functional queue to hold branching goals as the ctn
     [(failure? s) (values n answers p)]
     [(succeed? g) (if (succeed? ctn)
		       (values (fx1- n) (cons s answers) p)
		       (run-goal-dfs ctn s p n depth answers succeed))]
     [(zero? depth) (values n answers p)]
     [(conj? g) (run-goal-dfs (conj-lhs g) s p n depth answers (conj (conj-rhs g) ctn))]
     [(conde? g) (let-values ([(num-remaining answers p) (run-goal-dfs (conde-lhs g) s p n depth answers ctn)])
		   (if (zero? num-remaining) (values num-remaining answers p)
		       (run-goal-dfs (conde-rhs g) s p num-remaining depth answers ctn)))]
     [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)])
		    (run-goal-dfs g s p n (fx1- depth) answers ctn))]
     [(exist? g) (let-values ([(g s p) ((exist-procedure g) s p)])
		   (run-goal-dfs g s p n depth answers ctn))]
     [(fresh? g) (let-values ([(g s p) (g s p)])
		   (run-goal-dfs g s p n (fx1- depth) answers ctn))]
     [(trace-goal? g) (run-goal-dfs (trace-goal-goal g) s p n depth answers ctn)]
     [else (run-goal-dfs ctn (run-constraint g s) p n depth answers succeed)]))
    
    ;; === STREAMS ===
    
    (define (stream-step s p) ;TODO experiment with mutation-based mplus branch swap combined with answer return in one call
      (cert (stream? s) (package? p)) ; -> goal? stream? package?
      (exclusive-cond
       [(failure? s) (values s p)]
       [(state? s) (values s p)]
       [(bind? s) (let-values ([(s^ p) (stream-step (bind-stream s) p)])
		    (bind (bind-goal s) s^ p))]
       [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
		     (values (mplus (mplus-rhs s) lhs) p))]
       [(answers? s) (values (answers-cdr s) p)]
       [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))) 
