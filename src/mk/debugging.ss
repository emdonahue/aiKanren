(library (debugging)
  (export printfo)
  (import (chezscheme) (datatypes))

  (define (printfo . args)
    (apply printf args)
    succeed)
  
)
