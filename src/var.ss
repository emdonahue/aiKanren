(library (var)
  (export make-var var? var-id var-equal?)
  (import (chezscheme))

  (define-structure (var id))
  (define var-equal? equal?))
