(library (negation)
  (export noto)
  (import (chezscheme) (goals))

  (define (noto g)
    (assert (goal? g))
    (cond
     [(succeed? g) fail]
     [(fail? g) succeed])
    )
)
