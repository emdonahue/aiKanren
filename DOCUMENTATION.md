# Documentation
The overall library mk, which can be imported with `(import mk)` is composed of a number of sub-libraries. Importing mk imports all of the identifiers of all of these libraries. This documentation is broken down by sub-library, each with a brief description and a list of functions, parameters, or other important identifiers. Sub-libraries can be imported directly, for instance by developers working with the implementation itself, using the import statement specified under each sub-library heading.

- [core](#core)
- [constraints](#constraints)
- [lists](#lists)
- [interpreter](#interpreter)
- [tracing](#tracing)

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

## Constraints
```scheme
(import mk constraints)
```
This library implements a variety of common or useful constraints.
#### booleano
```scheme
(booleano x)
```
Constraints `x` to be either `#t` or `#f`.
#### absento
```scheme
(absento absent term)
```
Ensures that `absent` does not appear anywhere in `term`. Both can be arbitrary Scheme values containing logic variables.
#### presento
```scheme
(presento present term)
```
The inverse of `absento`. Ensures that `present` appears at least once in `term`.
#### finite-domain 
```scheme
(finite-domain x domain)
```
Ensures that `x` is one of the elements in `domain`. Both can be arbitrary miniKanren values.
#### ==> 
```scheme
(==> P Q)
```
Implements simple implicational logic -P v Q.
#### typeo
```scheme
(typeo x type?)
```
Ensures that `x` satisfies the arbitrary predicate `type?` when partially ground.
#### symbolo
```scheme
(symbolo x)
```
Ensures `x` is a symbol.
#### numbero
```scheme
(numbero x)
```
Ensures `x` is a number.
#### pairo
```scheme
(pairo x)
```
Ensures `x` is a pair.

## Interpreter
```scheme
(import mk interpreter)
```
This implementation includes a parameterizable interpreter for a subset of Scheme, which can be further customized through the use of parameters to interpret more precise subsets of Scheme.
#### evalo
```scheme
(evalo exp)
(evalo exp env)
(evalo exp env val)
```
Evaluates a Scheme program. The first two forms run their own internal miniKanren programs and return a single value. The final form is suited for use in a larger miniKanren program and accepts logic variables for all terms, returning a goal that must be combined with other goals and run using an appropriate `run` form.

`exp` represents the Scheme expression, possibly containing logic variables.
`env` is an environment represented as a list of key value pairs mapping names to values. The values are structured one of three possible ways:
- `('val . value)` contains a Scheme value or closure (represented by the list `('closure params body env)`).
- `('prim . id)` contains an identifier to one of the primitive functions implemented by the interpreter. The exported identifier `initial-environment` contains the starting list of such primitives, a subset of which can be used as the environment in calls to `evalo`.
- `('rec . (args body))` contains the arguments and body for a recursive function.
`val` is the logic variable bound to the output values of interpretation.

This library exports a large number of parameters for controlling the subset of Scheme interpreted. All parameters default to #t, infinity, or whatever value defines the most expressive possible subset of Scheme. This subset can therefore be restricted by setting values to #f or by limiting the integer as appropriate:
- interpreter/quote : Enables quotation
- interpreter/number : Enables numeric literals
- interpreter/boolean : Enables boolean literals
- interpreter/lambda : Enables lambda expressions
- interpreter/lambda/variadic : Enables variadic lambdas & applications
- interpreter/lambda/multi-arg : Enables 0, 1, or multi-argument lambdas & applications (when #f, all lambdas are one-argument)
- interpreter/if : Enables if expressions
- interpreter/if/non-null : Enables if expressions of non-null values (when #f, all if conditions must be explicitly booleans)
- interpreter/letrec : Enables letrec expressions

## Tracing
The tracing library exports a variety of useful debugging features, most notably the interface to the tracing system. The tracing system works by allowing the user to distribute named "trace goals" throughout their miniKanren program. When the search encounters these goals, assuming tracing is enabled, it logs the goal name to a trace inside the state. As states percolate through the search tree, they accumulate a trace that will be unique so long as all paths through the search are guaranteed to encounter a unique sequence of trace goals. 

Even though the search may interleave, each state's trace accumualtes in a predictable, linear fashion, and is therefore human-readable, allowing the user to accurately understand the path taken by any given state at any point in the execution. 

The trace generated by a single goal will be a list headed by that goal's name (`(name ...)`). The subsequent elements of that list will be sibling trace goals that are children of the top level trace goal. Hence, goals that are nested one within the other will return a nested list as their combined trace (`(name1 (name2 (name3)))`), while trace goals that appear at the same level will be siblings in their parent trace goal's list (`(name1 (name2) (name3))`).

Tracing is enabled with `trace-run` or `trace-run*`, which have the same syntax as their untraced variants. Currently, tracing always forces the search into a depth-first strategy in order to make the debug printing coherent. Eventually this will be relaxed when interleaving search gets its own conception of program tracing. Until then, however, it may be necessary to set the `max-depth` parameter to ensure termination.

By default, as the traced program runs, it will print out a nested outline describing every trace goal visited during the search. This outline is prefixed by * characters corresponding to the depth of the trace goal, and is intended to be browsed in software capable of managing collapsable outlines, such as Emacs org-mode. Every time a trace goal is encountered, it prints out a variety of views on the state at that point in the search. These include the goal name and definition, the current state of the substitution and constraint store, the current trace, and the answers returned by this branch of the search. Because the search is depth-first, the outline proceeds in order and answers generated deep within a branch are visible at all outline parents. This makes it possible to investigate which branch generated a given answer or which branches are not proceducing answers.

Logging goals exported by this package can be included during tracing to print arbitrary text at the relevant depth in the outline.

In addition to a trace of the entire program, it is possible to use proof goals to narrow down which parts of the space will be searched without affecting the contents of the substitution. A proof goal accepts a trace and ensures that all answers returned by its child goals conform to that trace. For example, to examine the behavior of a particular program synthesized by a relational interpreter, a common workflow is to run the trace interpreter with the ground program and collect the trace either directly from the state (using the `answer-type` parameter, or else from the trace output. The interpreter can then be re-run with a fresh program variable but with a proof goal that constrains it to follow only the path that synthesizes that particular program. This makes it possible to explore parts of the search space without corrupting the search behavior itself.

For developers working with the actual library source, the library supports a function similar to Chez Scheme's trace-* functions where define, lambda, cond, and a number of other forms support an org-* prefixed version. This causes them to print debugging information when tracing is enabled. Tracing can be forcibly enabled using the `org-trace` form, and internal functions will then print their arguments and return values at the appropriate level of the outline.

#### trace-goal
```scheme
(trace-goal name goal ...)
```
Runs all child goals while adding `name` to the trace.
#### trace-cond
```scheme
(trace-cond [name goal ...] [name2 goal ...])
```
A shortcut equivalent to a `conde` in which each branch is wrapped by a trace goal.
#### trace-run, trace-run*
Equivalent to `run` and `run*`  but enables tracing
#### prove
```scheme
(prove proof goal ...)
```
Runs child goals while ensuring that every state generates a subproof from those goals that matches proof. Proofs are most often extracted from returned states or trace printouts, but can be constructed manually. __ serves as the wildcard "cursor" that allows proofs to specify only a prefix and not a single concrete proof. 

The proof goal is usually used at the top level just below `trace-run`, but can be used to constrain sub parts of the program as well.
#### state-proof
A special accessor for extracting proofs from states.
### Logging
#### printfo
```scheme
(printfo ...)
```
A goal that passes its arguments to `printf` when evaluated. Printing only occurs when tracing is enabled.
#### displayo
```scheme
(displayo ...)
```
Prints the syntax of each expression along with their values at the appropriate level of the trace outline.
#### noopo
```scheme
(noopo ...)
````
A no-operation goal that does nothing but execute the code in its body when it is evaluated in the context of the search. May be useful for side-effecting code such as printing.
#### trace-goals
A parameter that enables or disables trace printing.
### Internal Debugging
#### org-trace
```scheme
(org-trace ...)
```
Enables trace printing even without the `trace-run` forms.
