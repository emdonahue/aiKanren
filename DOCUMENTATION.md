# Documentation
The overall library mk, which can be imported with `(import mk)` is composed of a number of sub-libraries. Importing mk imports all of the identifiers of all of these libraries. This documentation is broken down by sub-library, each with a brief description and a list of functions, parameters, or other important identifiers. Sub-libraries can be imported directly, for instance by developers working with the implementation itself, using the import statement specified under each sub-library heading.

## core
```scheme
(import (mk core))
```
Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.
Note too that in addition to the goal constructors listed here, any procedure can be used transparently as a goal (but not a constraint). The procedure must accept 3 arguments: the state containing the substitution and constraints, the package containing search-wide global data such as table data, and a goal representing the future goals in the current search. It must return 4 values: a goal that will be run immediately after return (or just the trivial **succeed** goal), the new state, the new package, and the new goal representing the future of the search.

### Variables
#### __
`__` is a wildcard variable that unifies with anything but does not modify the substitution.

### Goals
#### succeed
```scheme
succeed
```
The trivial succeed goal. This goal is a constant, not a function.
#### fail
```scheme
fail
```
The trivial fail goal. This goal is a constant, not a function.
#### ==
```scheme
(== x y)
```
Sound unification
#### conde
```scheme
(conde
  [goal ...]
  [goal ...]
  ...)
```
A disjunction between conjunctions of goals.
#### exist
```scheme
(exist (x y z) ...)
(exist () ...)
```
The most elementary way to introduce fresh variables. This goal simply instantiates one fresh variable per identifier in its binding form and runs its body goals with the fresh variables bound to those identifiers. With no identifiers, it can simply be used to conjoin its subgoals.
#### fresh
```scheme
(fresh (x y z) ...)
(fresh () ...)
```
Introduces fresh variables, like exist, but also forces the interleaving search to suspend before evaluating the body goals. Without variables, can be used to suspend the search manually.
### matcho
```scheme
(matcho ([(a . b) x] [('symbol 42 c) y] [c z]) ...)
```
A pattern matching form that can be used as a goal or constraint, and that is capable of introducing fresh variables. `matcho` works like other binding forms in that it binds a series of left-hand-side patterns to a series of right-hand-side values. The patterns can be composed of quoted symbols, numbers, bare identifiers, and lists or pairs of any of these, using the usual list and pair notations. `matcho` will destructure the right-hand-side values, if they are ground, and bind their contents to the matching identifiers in the goal body, after unifying any pattern constants with elements of the supplied values, as appropriate. 

If the right-hand-side values contain logic variables that cannot be destructured, `matcho` will unify those variables with reified versions of the patterns, with fresh logic variables bound to all unmatched identifiers. Identifiers can be reused to ensure unifiable values occur in the appropriate places in the input terms.

In many cases, `matcho` can replace--and should be preferred to--`fresh` due to its superior optimizations. If all right hand side values are fully ground, `matcho` does not suspend but continues evaluating its goal, which can significantly improve performance. Moreover, so long as the body of the `matcho` clause references only pattern variables, because it only destructures and renames terms, `matcho` will not diverge (barring trivial loops in the host language). However, there are times when it is necessary to reference external variables within the body of a `matcho`. At such times, it is adviseable to wrap the body of the `matcho` in an empty `fresh` to force a suspension of the search, unless it can be determined that divergence will not occur.

### Constraints
#### constraint
```scheme
(constraint ...)
```
Conjoins any number of ordinary goals and runs them as a constraint. Any goal aside from `fresh` and `exist` can be interpreted as a constraint. This means that rather than instantiating fresh variables and generating multiple search branches, the wrapped goals will wait until variables are instantiated by other parts of the search and only run until it can be determined that at least one of their branches is satisfied by the current substitution. This form allows arbitrarily complex constraints to be expressed as ordinary miniKanren relations and is one of the central capabilities of this implementation. This ability makes a number of otherwise difficult or impossible constraints trivial to write without modifying the constraint solving implementation. Example constraints can be found in the constraints library.
#### =/=
Disequality constraint
#### conj
```scheme
(conj x y)
```
A function that conjoins two goals or constraints.
#### disj
```scheme
(disj x y)
```
A function that disjoins two constraints. If applied to goals, they will be interpreted as constraints.
#### noto
```scheme
(noto g)
```
Negates a single goal or constraint, turning it into a negative constraint. Negated goals will be interpreted as constraints. A negated constraint operates like a generalized disequality. Negated conjunctions yield disjunctions of negated constraints. Negated disjunctions yield conjunctions of negated constraints. If the inner goal succeeds completely, the negated version will fail. If it fail, the negated version will succeed. If it is indeterminate, the negated version will suspend and wait until more variables are bound. Any goal that can be interpreted as a constraint can be negated.

### Run Interface
#### answer-type
A parameter that controls the answers returned by the run interface. It may take several values:
- 'reified (Default): Returns reified query variables, including reified versions of any constraints on those variables. These reified constraints will be the first order representations used internally.
- 'state : Returns the state objects corresponding to each answer. The state contains the substitution and constraint store as well as any other data specific to a single path through the search tree.
#### search-strategy
A parameter specifying the strategy to be used for the search.
- 'interleaving (Default): The standard miniKanren search
- 'dfs : A depth-first search that requires less overhead than the interleaving search, and so is faster in instances where all answers are desired. Can be combined with the `max-depth` parameter to create iterative deepening searches.
#### max-depth
A parameter controlling the max search depth before forced failure. Depth is calculated in terms of the size of the substitution, so this can be applied to both depth first and interleaving searches. No branch of the search can instantiate more free variables than the integer specified in `max-depth`. Default is unlimited depth.
#### run
```scheme
(run n (x y z) ...)
(run n x ...)
(run n () ...)
```
Runs the search and returns the first n answers. If the `answer-type` returns the query variables, they will be contained in a list in the order specified in the binding form. If the binding form is a single variable, then each answer will be a single value, not a list. `run` with an empty variable list will simply return as many empty lists as there are answers to be returned.
#### run*
```scheme
(run* (x y z) ...)
(run* x ...)
(run* () ...)
```
Returns all answers. Shortcut for:
```scheme
(parameterize ([search-strategy 'dfs]) (run -1 ...))
```
Always uses a depth first search for speed, although this may affect the order of returned answers. To force a different type of search, use `run` with -1 as the number of answers.
#### lazy-run
```scheme
(lazy-run (x y z) ...)
(lazy-run x ...)
(lazy-run () ...)
```
Returns a lazy stream representing the answers to the search specified by the body goals. Other lazy-* functions can be used to manipulate this stream.
#### lazy-run-null?
#t if the lazy stream is out of answers
#### lazy-run-car?
#t if the lazy stream has an answer ready
#### lazy-stream-car
Returns the current answer
#### lazy-stream-cdr
Advances the search stream by one step
#### lazy-stream-cdr*
Advances the search stream as many times as needed until it arrives at an answer or fails.

### Internals & Extensions
This section documents utilities for those trying to extend the language or otherwise working at a much deeper level with the internal representations.
#### var
```scheme
(var id)
```
Creates a new variable. `id` is an integer representing the variable's id number. Each fresh variable in a search has a unique id, which is tracked in the state. Variables are represented as vectors created by define-structure, and can be tested or accessed in the corresponding manner.
#### state
```scheme
(state substitution varid attributes)
```
A constructor for state objects defined with define-structure and implementing all the expected predicates and accessors. 

`substitution` is a skew binary random access list implemented internally.

`varid` represents the variable id of the most recently instantiated variable. Must be incremented before it can be used to create a new variable.

`attributes` contains the extensible attribute data that has been added to the state by external libraries, such as tracing.
#### state-attr
```scheme
(state-attr s attr?)
```
Retrieves an attribute from state `s` recognized by predicate attr?. Attributes are stored in a list, usually of structures created with define-structure, and are stored and retrieved by using the predicate generated with each structure. 
#### set-state-attr
```scheme
(set-state-attr s attr? attr)
```
Removes any previous attribute recognized by predicate `attr?` and installs the new attribute `attr`.

## Lists
```scheme
(import mk lists)
```
Contains a variety of useful functions for dealing with lists and trees in miniKanren.
#### appendo
```scheme
(appendo h t h+t)
```
Relational `append`.
#### assoco
```scheme
(assoco k kv v)
```
Relational `assoc`. Unifies `v` with the values of all pairs in `kv` for which `k` unifies with its key.
#### asspo
```scheme
(asspo k kv p)
```
Relational `assp`. For each pair in `kv` for which `k` unifies with its key, pass its value to the function `p`, which must return a goal.
#### listo
```scheme
(listo l)
```
A constraint that checks that `l` is a proper list.
#### for-eacho
```scheme
(for-eacho p xs)
```
A relational `for-each` constraint. Applies function `p` to each element of `xs`, which must return a constraint. Ensures that all elements of `xs` satisfy a given constraint.
#### membero
```scheme
(membero x xs)
```
A relational `member`. Unifies 'x' with all elements of `xs`.
#### filtero
```scheme
(filtero f xs ys)
```
A relational `filter`. Unifies `ys` with a list of all elements for which `f` produces a satisfiable constraint.
