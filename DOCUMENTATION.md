# Documentation
The overall library mk, which can be imported with `(import mk)` is composed of a number of sub-libraries. Importing mk imports all of the identifiers of all of these libraries. This documentation is broken down by sub-library, each with a brief description and a list of functions, parameters, or other important identifiers. Sub-libraries can be imported directly, for instance by developers working with the implementation itself, using the import statement specified under each sub-library heading.

## core
```scheme
(import (mk core))
```
Provides the fundamental forms of the language, including the run interface, the goal constructors, and the primitive constraint constructors.

### exist
```scheme
(exist (x y z) ...)
```
`exist` is the most elementary way to introduce fresh variables. This goal simply instantiates one fresh variable per identifier in its binding form and runs its body goals with the fresh variables bound to those identifiers. With no identifiers, it can simply be used to conjoin its subgoals.
