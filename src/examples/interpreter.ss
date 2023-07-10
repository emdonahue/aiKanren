(library (interpreter) ; Ported from https://github.com/michaelballantyne/faster-minikanren/blob/master/full-interp.scm
  (export evalo)
  (import (chezscheme) (aikanren))

  (define initial-env '())
  
  (define evalo
    (case-lambda
      [(expr) (evalo expr initial-env)]
      [(expr env) (run1 (val) (evalo expr env val))]
      [(expr env val)
       (conde
	 [(eval-quote expr env val)]
	 [(numbero expr) (== expr val)]
	 [(symbolo expr) (lookupo expr env val)]
	 [(eval-lambda expr env val)]
	 [(eval-prim expr env val)]
	 )]))

  (define (eval-quote expr env val)
    (fresh ()
      (== `(quote ,val) expr)
      (absento 'closure val)
      (absento 'prim val)
      (not-in-envo 'quote env)))
  
  (define (lookupo var env val) ;TODO can lookup be a constraint?
    (asspo var env 
	   (lambda (v)
	     (conde
	       [(== v `(val . ,val))]))))

  (define (eval-lambda expr env val)
    (fresh ()
     (matcho ([expr ('lambda args body)]) ;TODO enable environment variables in patterns with unquote
	     (== `(closure (lambda ,args ,body) ,env) val)
	     (constrain
	      (conde
		[(symbolo args)]
		[(for-eacho symbolo (lambda (x) (symbolo x)))])))
     (not-in-envo 'lambda env)))

  (define (not-in-envo sym env)
    (noto (asspo sym env (lambda (v) succeed))))

  (define (eval-prim expr env val)
    (conde
      [(eval-boolean expr env val)]
     ; [(eval-and expr env val)]
      ))

  (define (eval-boolean expr env val)
    (conde
      [(== #t expr) (== #t val)]
      [(== #f expr) (== #f val)]))

  (define (eval-and expr env val)
    3)
)