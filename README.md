# aiKanren
A performant miniKanren implementation designed to serve as a platform for AI research combining logical and probabilistic reasoning.
## Quick Start
In lieu of more extensive documentation, this section clarifies some differences from previous miniKanren systems for those already broadly familiar with miniKanren.

`make test` runs the tests. `make` compiles the library into a wpo in the lib subdirectory, which is only necessary if you want to compile your program with whole program optimization including this library. You can open a repl to experiment with using `make repl'. Run benchmarks with `make bench`.

To import the library in script mode for development, import `(aikanren)` and run your program with:

```scheme
scheme --libdirs aiKanren/src/mk --script "myprogram.ss"
```

The most important difference from other miniKanren implementations is that `fresh` is rarely used and not well supported. `exist` can be used as fresh that does not suspend (and so is not complete), and in most cases, when fresh is being used to destructure a list term, `matcho` can be used instead. `matcho` is a binding form used like so:

```scheme
(matcho ([x (h . t)]) ...)
```
This unifies x with a pair of two free variables and then runs the goals in ... in the lexical scope in which h and t are bound to those variables. Arbitrary list patterns that include numbers and symbols with `symbol are permitted as well. See matcho-tests.ss for examples.

The main reason this repository exists is the implementation of the forms `constraint` `pconstraint` and `noto`. See [this link](http://www.evandonahue.com/pdf/donahue_goalsasconstraints2023.pdf) for a paper explaining the details and the tests for numerous examples. See also the aikanren.ss exports for a complete list of functions and syntactic forms.

There is also a tracing function for debugging miniKanren programs. Usage is somewhat involved, but briefly, the tracer can be operated with:

```scheme
(trace-run (q) ...)
(trace-run depth (q) ...)
```

It operates in depth-first mode, so it is often better to start with a fully ground program or the optional depth parameter. Every time the search encounters a trace goal:

```scheme
(trace-goal name ...)
```

comprised of a name and an arbitrary list of goals, the search will print out various information about the substitution, constraint store, path taken to reach the goal, etc. `trace-conde` is a shorthand to place a tracegoal at every branch of a conde:

```scheme
(trace-conde [name ...] ...)
```

Printing will take the form of a nested outline with the number of leading * at the line start indicating the level of nesting. This is meant to be read in emacs org-mode, which will automatically interpret the output as a collapsible outline that can be browsed.

Because the 'conjunction passing' style of the interpreter executes both subgoals and right hand goals within the context of parent and left hand goals, it can be somewhat confusing where the execution trace is leading, which is why each level includes a 'proof' subheading that prints a more human readable trace of where in the execution of the program this goal was found.

Moreover, that proof can be copied and pasted back into the trace interpreter to constrain the search to only follow that path using the `prove` goal:

```scheme
(trace-run (q) (prove proof ...))
```

This makes it possible to test the behavior of the search down a particular branch without grounding variables, potentially changing the nature of the search. Answers returned by the trace-run form come paired with their proofs, so you can both understand how those answers were reached and feed them back in to the prove form to explore unconstrained search behavior that would lead to that result.

Examples can be found in tracing-tests.ss.

## Documentation
## Not Yet Implemented
-  simplify-=/= proceedure ([src/mk/solver.ss:147](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L147))
## TODO
- can we get guarded goal functionality by an == constraint and a schedule that when run unifies the guarded variables thereby triggering the unification? ([src/mk/aikanren.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/aikanren.ss#L1))
- do == and =/= automatically simplify when merged because we run constraints on the state not the substitution when reducing? ([src/mk/aikanren.ss:2](https://github.com/emdonahue/aiKanren/blob/main/src/mk/aikanren.ss#L2))
- bool is just true or false. does this automatically gel with =/= of the other one? ([src/mk/aikanren.ss:3](https://github.com/emdonahue/aiKanren/blob/main/src/mk/aikanren.ss#L3))
- we can get finite domain like ability to actually generate the answers by popping the constraint and treating it as a goal ([src/mk/aikanren.ss:4](https://github.com/emdonahue/aiKanren/blob/main/src/mk/aikanren.ss#L4))
- test whether optimize level works for whole library ([src/mk/aikanren.ss:5](https://github.com/emdonahue/aiKanren/blob/main/src/mk/aikanren.ss#L5))
- test for-eacho with xs^ shadowing xs once matcho identifiers are fixed ([src/mk/listo.ss:35](https://github.com/emdonahue/aiKanren/blob/main/src/mk/listo.ss#L35))
- does asspo need an extra argument to succeed if none found? eg disjoin with final goal? ([src/mk/listo.ss:42](https://github.com/emdonahue/aiKanren/blob/main/src/mk/listo.ss#L42))
- merge asspo matchos into single matcho once optimized ([src/mk/listo.ss:43](https://github.com/emdonahue/aiKanren/blob/main/src/mk/listo.ss#L43))
- can alist relations just be constraints if they only return 1 and use constraint semantics to terminate search? ([src/mk/listo.ss:44](https://github.com/emdonahue/aiKanren/blob/main/src/mk/listo.ss#L44))
- look at https://github.com/cisco/ChezScheme/issues/128 for discussion of other tracing options ([src/mk/utils.ss:49](https://github.com/emdonahue/aiKanren/blob/main/src/mk/utils.ss#L49))
- maybe fold org-tracing boolean into depth 0? ([src/mk/utils.ss:53](https://github.com/emdonahue/aiKanren/blob/main/src/mk/utils.ss#L53))
- make org-lambda check for optimization and remove itself to improve performance with debugging infrastructure in place ([src/mk/utils.ss:106](https://github.com/emdonahue/aiKanren/blob/main/src/mk/utils.ss#L106))
- simplify with negated pconstraints as well ([src/mk/reducer.ss:5](https://github.com/emdonahue/aiKanren/blob/main/src/mk/reducer.ss#L5))
- if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked ([src/mk/reducer.ss:21](https://github.com/emdonahue/aiKanren/blob/main/src/mk/reducer.ss#L21))
- in simplify matcho, can i just return the g case and let one fail be enough? ([src/mk/reducer.ss:58](https://github.com/emdonahue/aiKanren/blob/main/src/mk/reducer.ss#L58))
- should we thread the real state when expanding matcho while reducing ==? ([src/mk/reducer.ss:60](https://github.com/emdonahue/aiKanren/blob/main/src/mk/reducer.ss#L60))
- delete failure.ss ([src/mk/failure.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/failure.ss#L1))
- replace assert #f with useful error messages ([src/mk/goals.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L1))
- define a secondary run goal that runs children of conde and only that one should suspend fresh because it represents having to make a choice instead of pursuing a goal linearly into its depths ([src/mk/goals.ss:8](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L8))
- if we convert interleaving to cps, we can use the goal structure to store tracing info and trace the interleaving search without special affordances. might work if tracing goals just mutate rather than shadow params ([src/mk/goals.ss:9](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L9))
- if convert search to cps, can we use the results of walk to simplify the ctn and decide not to walk some of its goals? ([src/mk/goals.ss:10](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L10))
- do freshes that dont change the state preserve low varid count? ([src/mk/goals.ss:16](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L16))
- separate suspended into its own constraint and treat procedures as ad hoc goals to be run immediately. ad hoc goals that already guarantee normal form can simply return succeed and the new state/package ([src/mk/goals.ss:17](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L17))
- do freshes that dont change the state preserve low varid count? ([src/mk/goals.ss:18](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L18))
- check whether structural recursion check is needed anymore for matcho or if single state return is enough ([src/mk/goals.ss:25](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L25))
- move trace-goal to a procedure that checks for tracing params and only returns trace goal objects if tracing, otherwise noop and can remove from non tracing interpreters ([src/mk/goals.ss:33](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L33))
- use the ==s from constraints to simplify continuations in normal goal interpreter ([src/mk/goals.ss:34](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L34))
- consider making bind cps ([src/mk/goals.ss:49](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L49))
- consider analyzing goals in goal interpreter and running dfs if not recursive or only tail recursive. may require converting everything to cps. maybe use syntax analysis and a special conj type that marks its contents for dfs, where fresh bounces back to normal goal interpreter. it may not make a difference as outside of fresh a cps goal interpreter might be functionally depth first outside of trampolining ([src/mk/goals.ss:71](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L71))
- if we put run-goal-dfs in a parameter the tracing system will have a callback fn and we can trace without modifying the dfs ([src/mk/goals.ss:72](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L72))
- consider manipulating ctn order in dfs to get different searches, such as depth-ordered search using a functional queue to hold branching goals as the ctn ([src/mk/goals.ss:73](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L73))
- experiment with mutation-based mplus branch swap combined with answer return in one call ([src/mk/goals.ss:94](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L94))
- after optimizing matcho stopping only if branch detected, consider making that a merge point for a parallel execution where the other branch is put in the queue rather than an mplus ([src/mk/goals.ss:96](https://github.com/emdonahue/aiKanren/blob/main/src/mk/goals.ss#L96))
- first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable ([src/mk/matcho.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L1))
- consider a way to give matcho a global identity (maybe baking it into a defrel form?) so that matcho constraints with the same payload can simplify one another. eg, calling absento with the same payload on subparts of the same list many times ([src/mk/matcho.ss:2](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L2))
- integrate constraint substitutions with matcho ([src/mk/matcho.ss:12](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L12))
- generalize matcho-pair to multiple pairs, pairs with constant patterns, and other common patterns such as a-list ([src/mk/matcho.ss:30](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L30))
- specialize multiple pair matcho-pair on different modes (ground, free, etc) so we can always instantly destructure whatever is ground. may involve further manipulations of goal order based on mode ([src/mk/matcho.ss:32](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L32))
- can we make a generalized matcho out of matcho-pair on each pair of a pattern? ([src/mk/matcho.ss:33](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L33))
- specialize matcho for constraints vs goal & let interpreter decide implementation. constraint never needs to make fresh vars, goal doesn't need to know which vars are free (just whether) ([src/mk/matcho.ss:63](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L63))
- can we fire matcho immediately if its structural recursion instead of waiting on a conjunct ahead of it that may be all free? reordering conjuncts ([src/mk/matcho.ss:64](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L64))
- if matcho out-vars do not appear in the body, is there is no need to apply occurs-check constraints? ([src/mk/matcho.ss:68](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L68))
- allow matcho to match non pairs to allow constructing pairs from ground terms, and then =/= simplify should not fail on pairs for matcho ([src/mk/matcho.ss:88](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L88))
- add fender to matcho to prevent duplicate lhs vars and cyclic pattern vars (since out-vars are bound beneath in-vars, so the shadowing will go the wrong way) ([src/mk/matcho.ss:90](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L90))
- equip matcho with the patterns externally to fail constraints without invoking goal.  ([src/mk/matcho.ss:93](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L93))
- under what conditions should matcho continue? ([src/mk/matcho.ss:104](https://github.com/emdonahue/aiKanren/blob/main/src/mk/matcho.ss#L104))
- should minireify check eq or var? ([src/mk/mini-substitution.ss:59](https://github.com/emdonahue/aiKanren/blob/main/src/mk/mini-substitution.ss#L59))
- double check state exports. remove extend at least ([src/mk/state.ss:2](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L2))
- replace unbound with success as null element in state ([src/mk/state.ss:6](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L6))
- reify vars inside constraints ([src/mk/state.ss:10](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L10))
- is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify ([src/mk/state.ss:61](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L61))
- When should simplifying a constraint commit more ==? ([src/mk/state.ss:76](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L76))
- test whether eq checking the returned terms and just returning the pair as is without consing a new one boosts performance in unify ([src/mk/state.ss:85](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L85))
- unify should simplify constraints together as it conjoins them, or perhaps in solve-== after they have all been normalized ([src/mk/state.ss:91](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L91))
- return val constraint to simplify it with potentially other bindings and also unbind its var? ([src/mk/state.ss:102](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L102))
- see if the normalized ==s can help speed up occurs-check/binding, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification? ([src/mk/state.ss:116](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L116))
- try implementing occurs check in the constraint system and eliminating checks in the wrong id direction (eg only check lower->higher) ([src/mk/state.ss:117](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L117))
- add a non occurs check =!= or ==! ([src/mk/state.ss:118](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L118))
- remove double occurs check ([src/mk/state.ss:120](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L120))
- if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked ([src/mk/state.ss:146](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L146))
- in simplify matcho, can i just return the g case and let one fail be enough? ([src/mk/state.ss:165](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L165))
- should we thread the real state when expanding matcho while simplifying ==? ([src/mk/state.ss:168](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L168))
- refactor pconstraint solving/simplifying to share var iteration code among impls ([src/mk/state.ss:174](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L174))
- make == simplifier for pconstraints check for new vars ([src/mk/state.ss:179](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L179))
- how does disunify play with constraints in substitution? ([src/mk/state.ss:190](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L190))
- test whether all the manual checks for fail/succeed could be replaced by conj/disj macros ([src/mk/state.ss:209](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L209))
- consider sorting ids of variables before adding constraints to optimize adding to sbral. or possibly writing an sbral multi-add that does one pass and adds everything. would work well with sorted lists of attr vars to compare which constraints we can combine while adding ([src/mk/state.ss:220](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L220))
- can we store stale constraints? ([src/mk/state.ss:243](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L243))
- clean up state add constraint. remove dead code ([src/mk/state.ss:245](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L245))
- rename unbind-constraint -> remove-constraint ([src/mk/state.ss:254](https://github.com/emdonahue/aiKanren/blob/main/src/mk/state.ss#L254))
- delete datatypes.ss ([src/mk/datatypes.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L1))
- replace conj-car/cdr with lhs/rhs ([src/mk/datatypes.ss:21](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L21))
- make the var tag a unique object to avoid unifying with a (var _) vector and confusing it for a real var ([src/mk/datatypes.ss:49](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L49))
- try replacing state vector copy with manual updates using mutators ([src/mk/datatypes.ss:102](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L102))
- remove set-state-varid ([src/mk/datatypes.ss:121](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L121))
- rename state-or-failure? to maybe-state? ([src/mk/datatypes.ss:127](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L127))
- ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints. also break two pairs into a conj of ==. then we can simplify the order checking inside the unifier ([src/mk/datatypes.ss:149](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L149))
- see if normalize-matcho adds anything to solve-matcho ([src/mk/datatypes.ss:168](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L168))
- revisit goal-cond once fresh is either explicit or removed ([src/mk/datatypes.ss:203](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L203))
- replace conj with make-conj or short circuiting conj* where possible ([src/mk/datatypes.ss:239](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L239))
- experiment with short circuiting conj and disj macros ([src/mk/datatypes.ss:248](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L248))
- make conj a macro but when it is just an identifier macro make it return a function of itself for use with higher order fns ([src/mk/datatypes.ss:249](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L249))
- remove conj-car ([src/mk/datatypes.ss:265](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L265))
- is conj-fold ever used? ([src/mk/datatypes.ss:297](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L297))
- convert constructor fns to constructed params of structure   ([src/mk/datatypes.ss:307](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L307))
- microbenchmark disj cdr that looks ahead instead of using base case to check for non disj ([src/mk/datatypes.ss:323](https://github.com/emdonahue/aiKanren/blob/main/src/mk/datatypes.ss#L323))
- look into making large con/disjunctions of the same variable gather into a binary tree or something other than a random list and automatically build a decent data structure for it ([src/mk/constraints.ss:8](https://github.com/emdonahue/aiKanren/blob/main/src/mk/constraints.ss#L8))
- try ==> as =/=|== in case =/= might be more efficient for attribution/ ([src/mk/constraints.ss:12](https://github.com/emdonahue/aiKanren/blob/main/src/mk/constraints.ss#L12))
- do constraints need to manage recheck individually or is that just for matcho and disj? ([src/mk/constraints.ss:27](https://github.com/emdonahue/aiKanren/blob/main/src/mk/constraints.ss#L27))
- have typeo simplify == not simply succeed or fail ([src/mk/constraints.ss:39](https://github.com/emdonahue/aiKanren/blob/main/src/mk/constraints.ss#L39))
- create defconstraint that tags any matchos returned with the function pointer so they can dedup themselves ([src/mk/constraints.ss:108](https://github.com/emdonahue/aiKanren/blob/main/src/mk/constraints.ss#L108))
- can we remove trace-goal from general solver  ([src/mk/solver.ss:40](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L40))
- consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail ([src/mk/solver.ss:58](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L58))
- if we only get 1 binding in solve-==, it has already been simplified inside unify and we can skip it ([src/mk/solver.ss:59](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L59))
- can we simplify committed/pending as well and simplify already committed constraints from lower in the computation? ([src/mk/solver.ss:60](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L60))
- see if the normalized ==s can help speed up occurs-check/binding, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification? ([src/mk/solver.ss:89](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L89))
- try implementing occurs check in the constraint system and eliminating checks in the wrong id direction (eg only check lower->higher) ([src/mk/solver.ss:90](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L90))
- add a non occurs check =!= or ==! ([src/mk/solver.ss:91](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L91))
- add flag to let solve-disj know that its constraint might be normalized and to skip initial solving ([src/mk/solver.ss:108](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L108))
- is mini-unify necessary in solve-disj since the constraints should be normalized so we don't have two pairs? ([src/mk/solver.ss:123](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L123))
- add patterns to matcho and check them in simplify-=/= ([src/mk/solver.ss:131](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L131))
- can we discard proxies in some cases while reducing =/=? ([src/mk/solver.ss:148](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L148))
- replace walkvar in matcho solver with walk once matcho handles walks ([src/mk/solver.ss:177](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L177))
- this walk should be handled by == when it replaces var with new binding ([src/mk/solver.ss:178](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L178))
- if we get a non pair, we can fail matcho right away without expanding lambda ([src/mk/solver.ss:179](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L179))
- just operate on the list for matcho solving ([src/mk/solver.ss:183](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L183))
- split g in solve-disj into normalized and unnormalized args to let other fns flexibly avoid double solving already normalized constraints ([src/mk/solver.ss:186](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L186))
- deal with non left branching disjs that may be created dynamically by =/= or matcho. fundamentally we have to thread information from the first disj through to others and treat them linearly ([src/mk/solver.ss:193](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L193))
- can we just stash the pconstraint with the simplified under certain conditions if we know it wont need further solving? ([src/mk/solver.ss:215](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L215))
- make store constraint put disj right and everything else left ([src/mk/solver.ss:286](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L286))
- storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently ([src/mk/solver.ss:292](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L292))
- thread trace-goal through other critical infrastructure so its semantically transparent ([src/mk/solver.ss:297](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L297))
- create a defrel that encodes context information about what vars were available for use in reasoning about which freshes might be able to unify them within their lexical scope ([src/mk/solver.ss:299](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L299))
- do we need to check for recheckable matchos when attributing disj? ([src/mk/solver.ss:305](https://github.com/emdonahue/aiKanren/blob/main/src/mk/solver.ss#L305))
- Abstract out some of the math checks for navigating sbral ([src/mk/sbral.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/sbral.ss#L1))
- put the 0 somewhere else so sbral is more aesthetic when printed ([src/mk/sbral.ss:10](https://github.com/emdonahue/aiKanren/blob/main/src/mk/sbral.ss#L10))
- can sbral reference walk back up the list on the return from the recursion and rerecurse into nodes it visits along the way because early vars will always point to later vars? ([src/mk/sbral.ss:26](https://github.com/emdonahue/aiKanren/blob/main/src/mk/sbral.ss#L26))
- create special purpose upsert fns in sbral that let us set and conjoin a new constraint in one operation ([src/mk/sbral.ss:32](https://github.com/emdonahue/aiKanren/blob/main/src/mk/sbral.ss#L32))
- optimize sbral->alist/sbral->list ([src/mk/sbral.ss:77](https://github.com/emdonahue/aiKanren/blob/main/src/mk/sbral.ss#L77))
- refactor this library into 'vars' and other ([src/mk/ui.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/ui.ss#L1))
- make fresh insert fail checks between conjuncts to short circuit even building subsequent goals ([src/mk/ui.ss:10](https://github.com/emdonahue/aiKanren/blob/main/src/mk/ui.ss#L10))
- make conde do fail checks syntactically ([src/mk/ui.ss:19](https://github.com/emdonahue/aiKanren/blob/main/src/mk/ui.ss#L19))
- make fresh-vars non-recursive ala matcho ([src/mk/ui.ss:132](https://github.com/emdonahue/aiKanren/blob/main/src/mk/ui.ss#L132))
- make goal-cond automatically add a condition for trace goals when not compiling and make trace goals vanish when compiling (test (optimize-level) param? ([src/mk/tracing.ss:14](https://github.com/emdonahue/aiKanren/blob/main/src/mk/tracing.ss#L14))
- make all goals accept a list of states so that we can print only the code as written and the input and output states without having to multiplex the code points for the tracing interpreter ([src/mk/tracing.ss:30](https://github.com/emdonahue/aiKanren/blob/main/src/mk/tracing.ss#L30))
- DRY the matcho/exist/fresh calls to common calling interface. maybe use => cond interface ([src/mk/tracing.ss:39](https://github.com/emdonahue/aiKanren/blob/main/src/mk/tracing.ss#L39))
- might be able to fold proofs into standard dfs with parameters and get rid of special cps trace interpreter ([src/mk/tracing.ss:58](https://github.com/emdonahue/aiKanren/blob/main/src/mk/tracing.ss#L58))
- print unbound variables in substitution debugging by checking var id in state ([src/mk/tracing.ss:149](https://github.com/emdonahue/aiKanren/blob/main/src/mk/tracing.ss#L149))
- perhaps all constraint lookups receive pointers to a single store so that we can cheeply copy pointers to different attributed variables but only remove and apply the constraint once instead of copying the constraint and applying it many times ([src/mk/store.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/mk/store.ss#L1))
- == and =/= have different attributed variables, so each variable should store two lists. moreover, == are a superset of =/= so == list can just store the diff and then append them ([src/mk/store.ss:2](https://github.com/emdonahue/aiKanren/blob/main/src/mk/store.ss#L2))
- if we have a central constraint lookup with pointers, some constraints will simplify in place and so we can add them back with the same pointer without updating other pointers, while some will generate new constraints that need to be assigned to new pointers. we can perhaps diff the new and old constraints and only add to new pointers ([src/mk/store.ss:3](https://github.com/emdonahue/aiKanren/blob/main/src/mk/store.ss#L3))
- determine whether bind should halt after every fresh or only those that generate mplus/binds ([src/tests/goal-tests.ss:40](https://github.com/emdonahue/aiKanren/blob/main/src/tests/goal-tests.ss#L40))
- test reify cyclic once unsound unification implemented ([src/tests/goal-tests.ss:59](https://github.com/emdonahue/aiKanren/blob/main/src/tests/goal-tests.ss#L59))
- make  ([src/tests/goal-tests.ss:61](https://github.com/emdonahue/aiKanren/blob/main/src/tests/goal-tests.ss#L61))
- can we simplify disjunctions of == and =/= of the same var? technically should be simplified to x1 =/= 1 ([src/tests/solver-tests.ss:64](https://github.com/emdonahue/aiKanren/blob/main/src/tests/solver-tests.ss#L64))
- remove proxies from secondary vars in == ([src/tests/solver-tests.ss:241](https://github.com/emdonahue/aiKanren/blob/main/src/tests/solver-tests.ss#L241))
- revisit matcho eagerness if all ground ([src/tests/matcho-tests.ss:26](https://github.com/emdonahue/aiKanren/blob/main/src/tests/matcho-tests.ss#L26))
- make tassert capture file and line number ([src/tests/test-runner.ss:1](https://github.com/emdonahue/aiKanren/blob/main/src/tests/test-runner.ss#L1))
- test multi-success disj that should succeed instead of suspending as constraint. maybe normalize before starting constraint walk. maybe already handled by normalizing resulting constraint ([src/tests/constraints-tests.ss:2](https://github.com/emdonahue/aiKanren/blob/main/src/tests/constraints-tests.ss#L2))
- test that recursive disjunctions containing unifications dont run forever looking for a case that doesn't involve == when attributing/solving disjunctions ([src/tests/constraints-tests.ss:323](https://github.com/emdonahue/aiKanren/blob/main/src/tests/constraints-tests.ss#L323))
- quote/literal only needed if atoms in the output do not appear in the input ([src/examples/interpreter.ss:37](https://github.com/emdonahue/aiKanren/blob/main/src/examples/interpreter.ss#L37))
- can lookup be a constraint? ([src/examples/interpreter.ss:62](https://github.com/emdonahue/aiKanren/blob/main/src/examples/interpreter.ss#L62))
- enable environment variables in patterns with unquote ([src/examples/interpreter.ss:72](https://github.com/emdonahue/aiKanren/blob/main/src/examples/interpreter.ss#L72))
- can we use first order matcho to eliminate need for exist? ([src/examples/interpreter.ss:84](https://github.com/emdonahue/aiKanren/blob/main/src/examples/interpreter.ss#L84))
- can lookup be a constraint? ([src/examples/quine.ss:29](https://github.com/emdonahue/aiKanren/blob/main/src/examples/quine.ss#L29))
- enable environment variables in patterns with unquote ([src/examples/quine.ss:35](https://github.com/emdonahue/aiKanren/blob/main/src/examples/quine.ss#L35))
- merge optimized matchos ([src/examples/quine.ss:61](https://github.com/emdonahue/aiKanren/blob/main/src/examples/quine.ss#L61))
