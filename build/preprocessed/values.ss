;; Utilities for working with multiple value returns
(library (values)
  (export with-values first-value list-values values-ref)
  (import (chezscheme))

  (define-syntax with-values
    (syntax-rules ()
      [(_ vals proc) (call-with-values (lambda () vals) proc)]))

  (define-syntax first-value
    (syntax-rules ()
      [(_ vals) (with-values vals (lambda (first . rest) first))]))

  (define-syntax list-values
    (syntax-rules ()
      [(_ vals) (with-values vals list)]))

  (define-syntax values-ref
    (syntax-rules ()
      [(_ vals n) (list-ref (list-values vals) n)])))



