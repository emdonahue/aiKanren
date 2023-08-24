;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (reducer)
  (export reduce-constraint)
  (import (chezscheme) (datatypes) (mini-substitution))
  ;;TODO simplify with negated pconstraints as well

  (define (reduce-constraint g c s)
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]#;
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (simplify-unification (conj-lhs g) s)])
		  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
		      (let-values ([(simplified-rhs recheck-rhs) (simplify-unification (conj-rhs g) s)])
     (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]

     
     [(constraint? g) (reduce-constraint (constraint-goal g) c s)]
     [(procedure? g) (reduce-constraint (g empty-state empty-package) c s)]
     [(conde? g) (reduce-constraint (conde->disj g) c s)]
     [else (exclusive-cond
	    [(==? c) (reduce-== g c s)])])
    )

  (define (reduce-== g c s)
    (exclusive-cond
     [(==? g) (let-values ([(s simplified recheck) (mini-simplify s (==-lhs g) (==-rhs g) succeed succeed)])
		(values simplified recheck))])
    )

  )
