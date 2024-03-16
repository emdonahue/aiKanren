# Documentation
## core
```scheme
(import (mk core))
```
Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.
Note too that in addition to the goal constructors listed here, any procedure can be used transparently as a goal (but not a constraint). The procedure must accept 3 arguments: the state containing the substitution and constraints, the package containing search-wide global data such as table data, and a goal representing the future goals in the current search. It must return 4 values: a goal that will be run immediately after return (or just the trivial **succeed** goal), the new state, the new package, and the new goal representing the future of the search.
### Run
#### run
```scheme
(run n q g ...)
```
Runs a standard interleaving search and returns the first n answers.
#### run*
```scheme
(run* n q g ...)
```
Runs a standard interleaving search and returns the first n answers.
#### run1
```scheme
(run1 q g ...)
```
Returns the first answer instead of a list of answers. Returns (void) if no answers are returned. Useful to quickly obtain an answer without needing to check for failure.
### Lazy
#### lazy-run
```scheme
(lazy-run q g ...)
```
Returns a lazy-run stream object that represents a lazy search stream. The stream can be advanced using the lazy-run-* functions.
(lazy-run (q ...) g ...)
#### lazy-run-null?
```scheme
(lazy-run-null? _r_)
```
#### lazy-run-car?
```scheme
(lazy-run-car? _r_)
```
Returns the currently available answer, or void if none currently exists due to the stream being either indeterminate or exhausted.
#### lazy-run-car
```scheme
(lazy-run-car _r_)
```
Returns the currently available answer, or void if none currently exists due to the stream being either indeterminate or exhausted.
#### lazy-run-cdr
```scheme
(lazy-run-cdr _r_)
```
Advances the stream by one step. This may not yield an answer if the resulting stream is still indeterminate. Use lazy-run-car? to test whether the stream has an answer.
#### lazy-run-cdr*
```scheme
(lazy-run-cdr* _r_)
```
Advances the stream by one step. This may not yield an answer if the resulting stream is still indeterminate. Use lazy-run-car? to test whether the stream has an answer.
### Goals
#### succeed
A goal that trivially succeeds. Used as a constant rather than a function call.
#### fail
A goal that trivially fails. Used as a constant rather than a function call.
#### ==
```scheme
(== _x y_)
```
Implements unification between terms.
#### conde
```scheme
(conde (g ...))
```
```scheme
(conde c0 c ...)
```
Nondeterministic branching.
#### fresh
```scheme
(fresh q g ...)
```
Introduce fresh variables.
(fresh (x y z) ...)
Can be run with an empty variable list to simply suspend the search at that point.
#### exist
```scheme
(exist q g ...)
```
Equivalent to fresh, but does not suspend search. Only creates fresh variables.
(exist (x y z) ...)
#### matcho
A pattern-matching equivalent for fresh.
(matcho ([x (a . 1)] [y ('b . c)] ...) ...)
The above form destructures the input variables x and y, ensuring that (== (cdr x) 1) and (== (car y) 'b) and then binding a and c to the car and cdr of x and y respectively. a and b may then be accessed like normal let bindings within the scope of the wrapped goals.
In this implementation, the vast majority of fresh calls are better implemented as matcho calls. In addition to instantiating fresh variables and suspending the search as needed, matcho offers a convenient syntax for destructuring input terms---which is the most common use case for fresh---and performs various optimizations while doing so.
#### constraint
```scheme
(constraint g ...)
```
Wrapped goals are conjoined and interpreted as a constraint.
#### conj
```scheme
(conj _lhs rhs_)
```
Logical conjunction between goals or constraints.
Can be used between any goals or constraints. Unlike disj, conj is not specific to constraint goals.
#### disj
```scheme
(disj _lhs rhs_)
```
Logical disjunction between constraints.
Unlike conj, disj is specific to constraints and any goals joined with disj will be interpreted as constraints rather than as nondeterministic goals.
#### noto
```scheme
(noto _g_)
```
Logical negation of constraints.
Goals wrapped with noto will be interpreted as negated constraints. Negation in this context should be understood in terms of a few simple operations:
== and =/= become the other when negated
conj and disj become the other when negated and their children are negated in accordance with De Morgan's laws
primitive constraints (such as symbolo) become negated versions of themselves (e.g. not-symbolo)
matcho lazily waits until it can expand and then negates its expansion
fresh cannot currently be negated
#### =/=
```scheme
(=/= _lhs rhs_)
```
Disequality between terms.
### Quantification
#### __
Wildcard logic variable that unifies with everything without changing substitution.
### Parameters
#### answer-type
Defines the type of answers returned by run. May be 'reified for reified query variables or 'state for the entire internal state representation.
Default: 'reified
#### max-depth
Specifies the maximum search, beyond which the search branch will automatically terminate. Depth corresponds to the number of allocated fresh variables in the substitution. This parameter applies to all search types, including interleaving.
Default: (most-positive-fixnum).
#### search-strategy
Specifies the search strategy used by run. May be 'interleaving or 'dfs.
Default: 'interleaving.
