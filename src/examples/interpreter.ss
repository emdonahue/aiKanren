(library (interpreter) ; Ported from https://github.com/michaelballantyne/faster-minikanren/blob/master/full-interp.scm
  (export evalo initial-env)
  (import (chezscheme) (aikanren))

  (define empty-env '())
  (define initial-env `((list . (val . (closure (lambda x x) ,empty-env)))

			. ,empty-env))
  #;
  (			(not . (val . (prim . not)))
			(equal? . (val . (prim . equal?)))
			(symbol? . (val . (prim . symbol?)))
			(cons . (val . (prim . cons)))
			(null? . (val . (prim . null?)))
			(car . (val . (prim . car)))
			(cdr . (val . (prim . cdr))))
  
  (define evalo
    (case-lambda
      [(expr) (evalo expr '())]
      [(expr env) (run1 (val) (evalo expr (append env initial-env) val))]
      [(expr env val)
       (conde
	 [(eval-quote expr env val)]
	 [(numbero expr) (== expr val)]
	 [(symbolo expr) (lookupo expr env val)]
	 [(eval-lambda expr env val)]
;	 [(eval-prim expr env val)]
	 [(eval-apply expr env val)]
	 )]))

  (define (eval-quote expr env val)
    (fresh ()
      (== `(quote ,val) expr)
;      (absento 'closure val)
;      (absento 'prim val)
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
		[(for-eacho (lambda (x) (symbolo x)) args)])))
     (not-in-envo 'lambda env)))

  (define (eval-apply expr env val)
    (matcho
     ([expr (rator . rands)])
     (exist (closure) ;TODO can we use first order matcho to eliminate need for exist?
	    (evalo rator env closure)
	    (matcho
	     ([closure ('closure ('lambda params body) env^)])
	     (conde
	       [(symbolo params)
		(exist (arg)
		       (eval-listo rands env arg)
		       (evalo body `((,params . (val . ,arg)) . ,env^) val))]
	       [(pairo params)
		(extend-env params rands env env
			    (lambda (env^) (evalo body env^ val)))])))))
  
  (define (eval-prim expr env val)
    (conde
      [(eval-boolean expr env val)]
      [(matcho ([expr (and . e*)])
	       (not-in-envo 'and env)
	       (eval-and e* env val))]))

  (define (eval-boolean expr env val)
    (conde
      [(== #t expr) (== #t val)]
      [(== #f expr) (== #f val)]))

  (define (eval-and e* env val)
    (conde
      [(== e* '()) (== val #t)]))

  (define (not-in-envo sym env)
    (noto (asspo sym env (lambda (v) succeed))))

  (define (extend-env params rands env env^ ctn)
    (conde
      [(== params '()) (== rands '()) (ctn env^)]
      [(matcho ([params (p . ps)]
		[rands (r . rs)])
	       (exist (arg)
		      (evalo r env arg)
		      (extend-env ps rs env `((,p . (val . ,arg)) . ,env^) ctn)))]))
  
  (define (eval-listo expr env val)
    (conde
      [(== expr '()) (== val '())]
      [(matcho ([expr (e . es)]
		[val (v . vs)])
	       (evalo e env v)
	       (eval-listo es env vs))]))
)
