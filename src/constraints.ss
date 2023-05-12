(library (constraints)
  (export booleano presento)
  (import (chezscheme) (datatypes) (ui))

  (define (booleano v)
    (constrain (disj* (== v #t) (== v #f))))
  
  (define (presento container query)
    (constrain (== container query))
    )
  
)
