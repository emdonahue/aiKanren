(library (interpreter) ; Ported from https://github.com/michaelballantyne/faster-minikanren/blob/master/full-interp.scm
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
	 [(numbero expr) (== expr val)]
	 [(symbolo expr) (lookupo expr env val)]
	 [(eval-lambda expr env val)]
	 )]))

  (define (lookupo var env val)
    (asspo var env
	   (lambda (v)
	     (conde
	       [(== v `(val . ,val))]))))

  (define (eval-lambda expr env val)
    (matcho ([expr ('lambda args body)]) ;TODO enable environment variables in patterns with unquote
	    (== `(closure (lambda ,args ,body) ,env) val)
	    (constrain
	     (conde
	       [(symbolo args)]
	       [succeed]))))
)
