(library (constraints)
  (export empty-constraint-store disequality empty-disequality disequality-car disequality-cdr)
  (import (chezscheme))

  (define-structure (constraint-store constraints))
  (define-structure (constraint disequality type absento))
  
  (define empty-constraint-store (make-constraint-store '()))
  (define-values (empty-disequality disequality-car disequality-cdr disequality)
    (values '() car cdr (case-lambda
			  [(lhs rhs) (disequality lhs rhs empty-disequality)]
			  [(lhs rhs rest) (cons (cons lhs rhs) rest)])))

  
  )
