(library (runner)
  (export make-runner set-runner-stream runner? runner-stream runner-query runner-tables)
  (import (chezscheme) (failure))

  (define-structure (runner stream query tables))
  
  (define (set-runner-stream r s)
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r)))
