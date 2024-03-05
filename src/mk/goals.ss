(library (goals) ; Deals with the pure search aspects without constraints.
  (export run-goal run-goal-dfs stream-step)
  (import (chezscheme) (state) (failure) (package) (negation) (datatypes) (solver) (utils) (debugging)) 

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
                        ([(structurally-recursive? g s^ p) (expand-matcho g s p)]) ; TODO If any vars are non-free, there is structurally recursive information to exploit, so continue running aggressively on this branch. Otherwise suspend like a normal fresh.
                      (values (suspended (conj g ctn) s s^) p))]
       [(suspend? g) (values (make-suspended (conj (suspend-goal g) ctn) s) p)]
       ;; TODO use the ==s from constraints to simplify continuations in normal goal interpreter
       [else (let ([s (run-constraint g s)]) ; If constraints fail, return. Otherwise, run continuation.
               (if (failure? s) (values failure p) (run-goal ctn s p)))])]))

  (define (stream-step s p) ;TODO experiment with mutation-based mplus branch swap combined with answer return in one call
    (cert (stream? s) (package? p)) ; -> goal? stream? package?
    (exclusive-cond ;TODO after optimizing matcho stopping only if branch detected, consider making that a merge point for a parallel execution where the other branch is put in the queue rather than an mplus
     [(failure? s) (values s p)]
     [(state? s) (values failure p)]
     [(suspended? s) (run-goal (suspended-goal s) (suspended-state s) p)] 
     [(mplus? s) (let-values ([(lhs p) (stream-step (mplus-lhs s) p)])
                   (values (mplus (mplus-rhs s) lhs) p))]
     [(state+stream? s) (values (state+stream-stream s) p)]
     [else (assertion-violation 'stream-step "Unrecognized stream type" s)]))
  
  (define (mplus lhs rhs)
    ;; Interleaves two branches of the search
    (cert (stream? lhs) (stream? rhs)) ; ->stream? package?
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(state? lhs) (make-state+stream lhs rhs)] ; Float answers to the front of the tree
     [(state+stream? lhs) (make-state+stream (state+stream-state lhs) (mplus rhs (state+stream-stream lhs)))]
     [(state? rhs) (make-state+stream rhs lhs)]
     [(state+stream? rhs) (make-state+stream (state+stream-state rhs) (mplus lhs (state+stream-stream rhs)))]
     [else (make-mplus lhs rhs)]))


  ;; === DEPTH FIRST INTERPRETER ===

  
  (define run-goal-dfs
    (case-lambda
      [(g s p n depth)
       (let-values ([(num-answers answers p) (run-goal-dfs g s p n depth '() succeed)])
         (values answers p))]
      [(g s p n depth answers ctn) ; -> #answers answers package?
       ;;TODO consider analyzing goals in goal interpreter and running dfs if not recursive or only tail recursive. maybe use syntax analysis and a special conj type that marks its contents for dfs, where fresh bounces back to normal goal interpreter. it may not make a difference as outside of fresh a cps goal interpreter might be functionally depth first outside of trampolining
        (if (zero? depth) (values n answers p)
            (if (failure? s) (values n answers p)
                (exclusive-cond ; TODO consider manipulating ctn order in dfs to get different searches, such as depth-ordered search using a functional queue to hold branching goals as the ctn
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
                 [else (run-goal-dfs ctn (run-constraint g s) p n depth answers succeed)])))]))) 
