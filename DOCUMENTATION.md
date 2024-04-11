# Documentation
## core
### exist
```scheme
(exist (x y z) ...)
```
`exist` is the most elementary way to introduce fresh variables. This goal simply instantiates one fresh variable per identifier in its binding form and runs its body goals with the fresh variables bound to those identifiers. With no identifiers, it can simply be used to conjoin its subgoals.
