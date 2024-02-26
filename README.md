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

## TODO
A complete list of TODO items extracted from the source can be viewed [here](TODO.md).