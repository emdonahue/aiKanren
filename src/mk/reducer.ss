;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (reducer)
  (export reduce)
  (import (chezscheme))
  ;;TODO simplify with negated pconstraints as well
  (define (reduce g u)) 3)
