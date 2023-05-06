(library (runner)
  (export make-runner set-runner-stream runner? runner-stream runner-query runner-package)
  (import (chezscheme) (failure))

  (define-structure (runner stream query package))
  
  (define (set-runner-stream r s)
    (assert (and (runner? r) (not (runner? s))))
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r)))
