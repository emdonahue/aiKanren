;TODO delete datatypes.ss
(library (datatypes)
  (export succeed fail succeed? fail?)
  (import (chezscheme))

  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))
  
)
