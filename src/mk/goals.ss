(library (goals) ; Deals with the pure search aspects without constraints.
  (export run-goal run-goal-dfs stream-step)
  (import (chezscheme) (state) (failure) (package) (store) (negation) (datatypes) (solver) (utils) (debugging)) 

  ;; === INTERLEAVING INTERPRETER ===
  
  (define run-goal
    ;; Converts a goal into a stream. Primary interface for evaluating goals using interleaving search.
    ;;TODO define a secondary run goal that runs children of conde and only that one should suspend fresh because it represents having to make a choice instead of pursuing a goal linearly into its depths
    ;;TODO if we convert interleaving to cps, we can use the goal structure to store tracing info and trace the interleaving search without special affordances. might work if tracing goals just mutate rather than shadow params
    ;;TODO if convert search to cps, can we use the results of walk to simplify the ctn and decide not to walk some of its goals?
    (org-case-lambda
     run-goal
     [(g s p) (run-goal g s p succeed)] ; Create an empty 'succeed' continuation representing the future conjuncts. This interpreter is written in "conjunction passing style," so rather than binding the lhs of a conj to the stream of the rhs, we run the lhs, passing in the conjunction of its rhs and the current continuation (ctn) to be evaluated later. 
     [(g s p ctn)
      (cert (goal? g) (or (fail? g) (state? s)) (package? p)) ; -> stream? package?      
      (exclusive-cond
       [(succeed? g) (if (succeed? ctn) (values s p) (run-goal ctn s p))] ; If the ctn is empty, we're done. Otherwise, now we run it.
       [(conj? g) (run-goal (conj-lhs g) s p (conj (conj-rhs g) ctn))] ; Run the lhs while pushing the rhs onto the continuation.
       [(procedure? g) (let-values ([(g s p) (g s p)])
                     (run-goal g s p ctn))] ; Any procedure that accepts a state and package and returns a goal, state, and package can be considered a goal. Fresh and exist are implemented in terms of such procedures.
       [(conde? g) (let*-values ; Although states are per branch, package is global and must be threaded through lhs and rhs.
                       ([(lhs p) (run-goal (conde-lhs g) s p ctn)]
                        [(rhs p) (run-goal (conde-rhs g) s p ctn)])
                     (values (mplus lhs rhs) p))]
       [(matcho? g) (let-values ;TODO check whether structural recursion check is needed anymore for matcho or if single state return is enough
                        ([(structurally-recursive? g s^ p) (expand-matcho g s p)]) 
                      (if structurally-recursive?
                          (suspendm (conj g ctn) s^ p s) ;(run-goal g s^ p)
                          (suspendm (conj g ctn) s^ p s))
                      #;
                      (if (and #f structurally-recursive?) ; If any vars are non-free, there is structurally recursive information to exploit, ;
                      (run-goal g s^ p) ; so continue running aggressively on this branch. ;
                      (suspend g s^ p s)))] ; Otherwise suspend like a normal fresh.
       [(suspend? g) (values (make-suspended (conj (suspend-goal g) ctn) s) p)]
       [(trace-goal? g) (run-goal (trace-goal-goal g) s p ctn)] ;TODO move trace-goal to a procedure that checks for tracing params and only returns trace goal objects if tracing, otherwise noop and can remove from non tracing interpreters
       ;; TODO use the ==s from constraints to simplify continuations in normal goal interpreter
       [else (let ([s (run-constraint g s)]) ; If constraints fail, return. Otherwise, run continuation.
               (if (failure? s) (values failure p) (run-goal ctn s p)))])]))
  
  (define (mplus lhs rhs)
    ;; Interleaves two branches of the search
    (cert (stream? lhs) (stream? rhs)) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(state? lhs) (make-state+stream lhs rhs)] ; Float answers to the front of the tree
     [(state+stream? lhs) (make-state+stream (state+stream-car lhs) (mplus rhs (state+stream-cdr lhs)))]
     [(state? rhs) (make-state+stream rhs lhs)]
     [(state+stream? rhs) (make-state+stream (state+stream-car rhs) (mplus lhs (state+stream-cdr rhs)))]
     [else (make-mplus lhs rhs)]))


  (define (suspendm g s^ p s)
    ;; Suspends the goal g as a suspended stream. Used by fresh etc to pass control to other search branches.
    (cert (goal? g) (state-or-failure? s^) (package? p) (state? s))
    (exclusive-cond
     [(fail? g) (values failure p)]
     [(succeed? g) (values s p)] ; Trivial successes can throw away any var ids reserved for fresh vars, as the substitution will never see them. Therefore, return old state s.
     [else (values (make-suspended g s^) p)]))

  ;; === DEPTH FIRST INTERPRETER ===

  (define (run-goal-dfs g s p n depth answers ctn) ;TODO consider analyzing goals in goal interpreter and running dfs if not recursive or only tail recursive. maybe use syntax analysis and a special conj type that marks its contents for dfs, where fresh bounces back to normal goal interpreter. it may not make a difference as outside of fresh a cps goal interpreter might be functionally depth first outside of trampolining
    ;;TODO if we put run-goal-dfs in a parameter the tracing system will have a callback fn and we can trace without modifying the dfs
    (if (zero? depth) (values n answers p)
     (exclusive-cond ; TODO consider manipulating ctn order in dfs to get different searches, such as depth-ordered search using a functional queue to hold branching goals as the ctn
      [(failure? s) (values n answers p)]
      [(succeed? g) (if (succeed? ctn)
                        (values (fx1- n) (cons s answers) p)
                        (run-goal-dfs ctn s p n depth answers succeed))]
      [(conj? g) (run-goal-dfs (conj-lhs g) s p n depth answers (conj (conj-rhs g) ctn))] ; Conj rhs to continuation.
      [(conde? g) (let-values ([(num-remaining answers p) (run-goal-dfs (conde-lhs g) s p n depth answers ctn)])
                    (if (zero? num-remaining) (values num-remaining answers p)
                        (run-goal-dfs (conde-rhs g) s p num-remaining depth answers ctn)))]
      [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)])
                     (run-goal-dfs g s p n (fx1- depth) answers ctn))]
      [(procedure? g) (let-values ([(g s p) (g s p)])
                        (run-goal-dfs g s p n (fx1- depth) answers ctn))]
      [(suspend? g) (run-goal-dfs (suspend-goal g) s p n depth answers ctn)]
      [(trace-goal? g) (run-goal-dfs (trace-goal-goal g) s p n depth answers ctn)]
      [else (run-goal-dfs ctn (run-constraint g s) p n depth answers succeed)])))
  
  ;; === STREAMS ===
  
  (define (stream-step s p) ;TODO experiment with mutation-based mplus branch swap combined with answer return in one call
    (cert (stream? s) (package? p)) ; -> goal? stream? package?
    (exclusive-cond ;TODO after optimizing matcho stopping only if branch detected, consider making that a merge point for a parallel execution where the other branch is put in the queue rather than an mplus
     [(failure? s) (values s p)]
     [(state? s) (values s p)]
     #;
     [(suspended? s) (let-values ([(s^ p) (stream-step (suspended-stream s) p)]) ;
     (suspended (suspended-goal s) s^ p))]
     [(suspended? s) (run-goal (suspended-goal s) (suspended-state s) p)] ;TODO rename suspended to suspended
     [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
                   (values (mplus (mplus-rhs s) lhs) p))]
     [(state+stream? s) (values (state+stream-cdr s) p)]
     [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))) 
