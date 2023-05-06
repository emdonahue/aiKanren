(library (package)
  (export package? empty-package)
  (import (chezscheme))

  (define-structure (package tables))
  (define empty-package (make-package '())))
