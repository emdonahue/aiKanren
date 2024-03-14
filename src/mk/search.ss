(library (search) ; Deals with the pure search aspects without constraints.
  (export run-goal run-goal-dfs stream-step max-depth)
  (import (chezscheme) (state) (failure) (package) (negation) (goals) (streams) (matcho) (solver) (utils) (debugging)) 

  (define max-depth ; Specifies the maximum search, beyond which the search branch will automatically terminate. Depth corresponds to the number of allocated fresh variables in the substitution. This parameter applies to all search types, including interleaving.
    ; Default: (most-positive-fixnum).
    (make-parameter (most-positive-fixnum)
                    (lambda (d) (unless (integer? d) (assertion-violation 'max-depth "max-depth must be an integer" d)) d)))
  
  ;; === INTERLEAVING INTERPRETER ===
  
  (define run-goal
    ;; Converts a goal into a stream. Primary interface for evaluating goals using interleaving search.
    ;;TODO define a secondary run goal that runs children of conde and only that one should suspend fresh because it represents having to make a choice instead of pursuing a goal linearly into its depths
    ;;TODO if we convert interleaving to cps, we can use the goal structure to store tracing info and trace the interleaving search without special affordances. might work if tracing goals just mutate rather than shadow params
    ;;TODO if convert search to cps, can we use the results of walk to simplify the ctn and decide not to walk some of its goals?
    (case-lambda
     [(g s p) (run-goal g s p succeed)] ; Create an empty 'succeed' continuation representing the future conjuncts. This interpreter is written in "conjunction passing style," so rather than binding the lhs of a conj to the stream of the rhs, we run the lhs, passing in the conjunction of its rhs and the current continuation (ctn) to be evaluated later. 
     [(g s p ctn)
      (cert (goal? g) (or (fail? g) (state? s)) (package? p)) ; -> stream? package?      
      (exclusive-cond
       [(succeed? g) (if (succeed? ctn) (values s p) (run-goal ctn s p))] ; If the ctn is empty, we're done. Otherwise, now we run it.
       [(conj? g) (run-goal (conj-lhs g) s p (conj (conj-rhs g) ctn))] ; Run the lhs while pushing the rhs onto the continuation.
       [(procedure? g) (let-values ([(g s p ctn) (g s p ctn)])
                         (if (exceeds-max-depth? s) (values failure p)
                          (run-goal g s p ctn)))] ; Any procedure that accepts a state and package and returns a goal, state, and package can be considered a goal. Fresh and exist are implemented in terms of such procedures.
       [(conde? g) (let*-values ; Although states are per branch, package is global and must be threaded through lhs and rhs.
                       ([(lhs p) (run-goal (conde-lhs g) s p ctn)]
                        [(rhs p) (run-goal (conde-rhs g) s p ctn)])
                     (values (mplus lhs rhs) p))]
       [(matcho? g) (let-values ;TODO check whether structural recursion check is needed anymore for matcho or if single state return is enough
                        ([(structurally-recursive? g s^ p) (expand-matcho g s p)]) ; TODO If any vars are non-free, there is structurally recursive information to exploit, so continue running aggressively on this branch. Otherwise suspend like a normal fresh.
                      (if (exceeds-max-depth? s) (values failure p)
                          (values
                           (exclusive-cond
                            [(fail? g) failure]
                            [(succeed? g) s]     
                            [else (make-suspended (conj g ctn) s^)]) p)))]
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
    (case-lambda ;TODO perhaps instead of counting freshes we could just limit the max var id to serve as a depth proxy
      [(g s p n)
       (let-values ([(num-answers answers p) (run-goal-dfs g s p n '() succeed)])
         (values answers p))]
      [(g s p n answers ctn) ; -> #answers answers package?
       ;;TODO consider analyzing goals in goal interpreter and running dfs if not recursive or only tail recursive. maybe use syntax analysis and a special conj type that marks its contents for dfs, where fresh bounces back to normal goal interpreter. it may not make a difference as outside of fresh a cps goal interpreter might be functionally depth first outside of trampolining
        (if (failure? s) (values n answers p)
            (exclusive-cond ; TODO consider manipulating ctn order in dfs to get different searches, such as depth-ordered search using a functional queue to hold branching goals as the ctn
             [(succeed? g) (if (succeed? ctn)
                               (values (fx1- n) (cons s answers) p)
                               (run-goal-dfs ctn s p n answers succeed))]
             [(conj? g) (run-goal-dfs (conj-lhs g) s p n answers (conj (conj-rhs g) ctn))] ; Conj rhs to continuation.
             [(conde? g) (let-values ([(num-remaining answers p) (run-goal-dfs (conde-lhs g) s p n answers ctn)])
                           (if (zero? num-remaining) (values num-remaining answers p)
                               (run-goal-dfs (conde-rhs g) s p num-remaining answers ctn)))]
             [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)])
                            (if (exceeds-max-depth? s) (values n answers p)
                                (run-goal-dfs g s p n answers ctn)))]
             [(procedure? g) (let-values ([(g s p ctn) (g s p ctn)])
                               (if (exceeds-max-depth? s) (values n answers p)
                                   (run-goal-dfs g s p n answers ctn)))]
             [(suspend? g) (run-goal-dfs (suspend-goal g) s p n answers ctn)]
             [(dfs-goal? g) ((dfs-goal-procedure g) s p n answers ctn)]
             [else (run-goal-dfs ctn (run-constraint g s) p n answers succeed)]))]))

  (define (exceeds-max-depth? s)
    (cert (maybe-state? s))
    (or (failure? s) (fx< (max-depth) (state-varid s))))) 
