(library (constraints)
  (export empty-constraint-store)
  (import (chezscheme))

  (define-structure (constraint-store constraints))
  (define empty-constraint-store (make-constraint-store '()))
  
  (define-structure (constraint disequality type absento))
  )
