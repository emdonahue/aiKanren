(library (interpreter)
  (export evalo)
  (import (chezscheme) (aikanren))

  (define evalo
    (case-lambda
      [(expr env val)
       (conde
	 [((== `(quote val) expr))]
	 )]))
)
