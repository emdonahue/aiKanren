# Documentation
The overall library mk, which can be imported with `(import mk)` is composed of a number of sub-libraries. Importing mk imports all of the identifiers of all of these libraries. This documentation is broken down by sub-library, each with a brief description and a list of functions, parameters, or other important identifiers. Sub-libraries can be imported directly, for instance by developers working with the implementation itself, using the import statement specified under each sub-library heading.

## core
```scheme
(import (mk core))
```
Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.
Note too that in addition to the goal constructors listed here, any procedure can be used transparently as a goal (but not a constraint). The procedure must accept 3 arguments: the state containing the substitution and constraints, the package containing search-wide global data such as table data, and a goal representing the future goals in the current search. It must return 4 values: a goal that will be run immediately after return (or just the trivial **succeed** goal), the new state, the new package, and the new goal representing the future of the search.
### exist
```scheme
(exist (x y z) ...)
```
`exist` is the most elementary way to introduce fresh variables. This goal simply instantiates one fresh variable per identifier in its binding form and runs its body goals with the fresh variables bound to those identifiers. With no identifiers, it can simply be used to conjoin its subgoals.
