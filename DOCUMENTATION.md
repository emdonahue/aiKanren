# Documentation
-  Goals
 - [succeed](#succeed)
 - [fail](#fail)
 - [==](#==)
 - [conde](#conde)
 - [fresh](#fresh)
-  Constraints
 - [conj](#conj)
 - [disj](#disj)
 - [noto](#noto)
 - [=/=](#=/=)
 - [booleano](#booleano)
 - [presento](#presento)
 - [absento](#absento)
 - [listo](#listo)
 - [finite-domain](#finite-domain)
 - [==>](#==>)
 - [typeo](#typeo)
 - [symbolo](#symbolo)
 - [numbero](#numbero)
 - [pairo](#pairo)
-  List
 - [membero](#membero)
 - [appendo](#appendo)
 - [assoco](#assoco)
 - [asspo](#asspo)
 - [for-eacho](#for-eacho)
-  Quantification
 - [__](#__)
-  Debugging
 - [printfo](#printfo)
 - [displayo](#displayo)
 - [noopo](#noopo)
 - [trace-goal](#trace-goal)
 - [trace-run](#trace-run)
 - [trace-conde](#trace-conde)
 - [prove](#prove)
 - [trace-proof-goals](#trace-proof-goals)
 - [trace-goals](#trace-goals)
 - [var](#var)
-  Parameters
 - [reify-constraints](#reify-constraints)
## Goals
### succeed\n```scheme
  (define succeed ; A goal that trivially succeeds. Used as a constant rather than a function call.
```
### fail\n```scheme
  (define fail ; A goal that trivially fails. Used as a constant rather than a function call.
```
### ==\n```scheme
  (define (== x y) ; Implements unification between terms.
```
### conde\n```scheme
 (define-syntax conde ; Nondeterministic branching.
```
### fresh\n```scheme
  (define-syntax fresh ; Introduce fresh variables.
    ;; (fresh (x y z) ...) 
```
## Constraints
### conj\n```scheme
  (define (conj lhs rhs) ; Logical conjunction between goals or constraints.
    ;; Can be used between any goals or constraints. Unlike disj, conj is not specific to constraint goals.
```
### disj\n```scheme
  (define (disj lhs rhs) ; Logical disjunction between constraints.
    ; Unlike conj, disj is specific to constraints and any goals joined with disj will be interpreted as constraints rather than as nondeterministic goals.
```
### noto\n```scheme
  (define (noto g) ; Logical negation of constraints.
    ;; Goals wrapped with noto will be interpreted as negated constraints. Negation in this context should be understood in terms of a few simple operations:
    ;; == and =/= become the other when negated
    ;; conj and disj become the other when negated and their children are negated in accordance with De Morgan's laws
    ;; primitive constraints (such as symbolo) become negated versions of themselves (e.g. not-symbolo)
    ;; matcho lazily waits until it can expand and then negates its expansion
    ;; fresh cannot currently be negated
```
### =/=\n```scheme
  (define (=/= lhs rhs) ; Disequality between terms.
```
### booleano\n```scheme
  (define (booleano v) ; Constrains a term to be either #t or #f.
```
### presento\n```scheme
  (define (presento present term) ; Constrains term so that it must contain present. Logical negation of absento.
```
### absento\n```scheme
  (define (absento absent term) ; Constrains term so that absent cannot appear anywhere within it. Logical negation of presento.
```
### listo\n```scheme
  (define (listo l) ; Constrains l to be a proper list.
```
### finite-domain\n```scheme
  (define (finite-domain v ds) ; Constrains v to be one of the elements of ds. ds may contain logic variables.
```
### ==>\n```scheme
  (define (==> antecedent consequent) ; Simple implication. Equivalent to (disj (noto antecedent) consequent).
```
### typeo\n```scheme
  (define (typeo v t?) ; Constrains v to be of type t?, where t? is a type predicate.
```
### symbolo\n```scheme
  (define (symbolo v) ; Constrains v to be a symbol.
```
### numbero\n```scheme
  (define (numbero v) ; Constrains v to be a pair.
```
### pairo\n```scheme
  (define (pairo v) ; Constrains v to be a pair.
```
## List
### membero\n```scheme
  (define (membero x xs) ; Generates all lists xs containing x at least once.
```
### appendo\n```scheme
  (define (appendo h t ht) ; Appends h and t, yielding ht.
```
### assoco\n```scheme
  (define (assoco x xs o) ;; Unifies x with all keys of alist xs for which o unifies with the value. Analogous to Scheme assoc.
```
### asspo\n```scheme
  (define (asspo x xs proc) ; Binds x to all keys of alist xs for which proc does not fail on the value. Analogous to Scheme assp.
```
### for-eacho\n```scheme
  (define (for-eacho proc xs) ; Applies proc to each element of xs.
```
## Quantification
### __\n```scheme
  (define __ ; Wildcard logic variable that unifies with everything without changing substitution.
```
## Debugging
### printfo\n```scheme
  (define (printfo . args) ; A no-op goal that prints its arguments as part of the debug logging system.
```
### displayo\n```scheme
  (define-syntax displayo ; A no-op goal that reifies and displays its arguments as part of the debug logging system.
```
### noopo\n```scheme
  (define-syntax noopo ; A no-op goal that executes arbitrary code when called as part of the search.
```
### trace-goal\n```scheme
  (define-syntax trace-goal ; Wraps one or more goals and adds a level of nesting to the trace output.
    ;; (trace-goal name goals...)
    ;; When the trace is printing, goals wrapped in trace-goal will print within a nested hierarchy under a new heading titled <name>.
```
### trace-run\n```scheme
   (define-syntax trace-run ; Equivalent to run**-dfs or run*-dfs, but activates tracing system.
     ;; (trace-run (q) g ...)
     ;; (trace-run max-depth (q) g ...)
     ;; The tracing system prints nested debugging information including which trace-goals have been encountered, and various views of the substitution and constraints at each trace-goal. Output is formatted with line-initial asterisks, and is intended to be viewed in a collapsible outline viewer such as Emacs org mode.
```
### trace-conde\n```scheme
  (define-syntax trace-conde ; Equivalent to conde but each branch begins with a name and implicitly instantiates a trace-goal.
    ;; (trace-conde [name1 g1 ...] [name2 g2 ...] ...)
```
### prove\n```scheme
  (define-syntax prove ; Asks the tracing interpreter to prove a particular path through the program.
    ;; (trace-run (q) (prove <(partial) proof generated by previous trace-run> g ...))
    ;; During tracing, each trace-goal encountered prints a proof that records what program path through other trace goals was taken to arrive at that goal. At intermediate trace-goals, the path is open ended (ending in a __). The trace-run interpreter also returns complete proofs with its final answers. Any of these proofs can be copied verbatim and pasted into the prove goal to enforce that any wrapped goals will fail if they deviate from this proof path. The purpose of this goal is to allow the user to incrementally constrain paths through the search so as to debug deep parts of the search space by skipping searches in other parts of the space.
```
### trace-proof-goals\n```scheme
  (define trace-proof-goals (make-parameter #t)) ; A flag to enable or disable use of the proof subsystem during tracing.
  (define trace-goals (make-parameter #t)) ; A flag to enable or disable trace printing.
  (define-structure (trace-answer theorem proof state))
```
### trace-goals\n```scheme
  (define trace-goals (make-parameter #t)) ; A flag to enable or disable trace printing.
  (define-structure (trace-answer theorem proof state))
```
### var\n```scheme
  (define var ; Accepts an integer var-id and creates a var struct. Mostly for internal use, or for dynamically generating miniKanren programs.
      [(_ (var . idspec) body ...) (define var (org-lambda var idspec body ...))])))
```
## Parameters
### reify-constraints\n```scheme
  (define reify-constraints ; If #f, constraints are not printed during reification. Situationally useful when dealing with very large constraints.
    ; Default: #t
```
