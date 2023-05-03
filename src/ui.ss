(library (ui)
  (export == conde)
  (import (chezscheme) (goals))

  (define (== x y)
    (make-unification x y))

  (define (conde x y)
    (make-disj x y))
  
)
