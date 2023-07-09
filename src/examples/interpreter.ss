(library (interpreter)
  (export evalo)
  (import (chezscheme) (aikanren))

  (define initial-env '())
  
  (define evalo
    (case-lambda
      [(expr) (run1 (val) (evalo expr initial-env val))]
      [(expr val) (evalo expr initial-env val)]
      [(expr env val)
       (conde
	 [(== `(quote ,val) expr)]
	 )]))
)
