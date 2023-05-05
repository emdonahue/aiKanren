(library (var)
  (export make-var var? var-id unbound unbound?)
  (import (chezscheme))

  (define-structure (var id))
  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v)))
