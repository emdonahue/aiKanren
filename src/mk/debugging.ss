(library (debugging)
  (export printfo noopo)
  (import (chezscheme) (datatypes))

  (define (printfo . args)
    (noopo (apply printf args)))

  (define (noopo . args)
    succeed)
  
)
