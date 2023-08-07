(library (interpreter) ; Ported from https://github.com/michaelballantyne/faster-minikanren/blob/master/full-interp.scm
  (export evalo initial-env evalo-env)
  (import (chezscheme) (aikanren))

  (define empty-env '())
  (define initial-env `((list . (val . (closure (lambda x x) ,empty-env)))
			(cons . (val . (prim . cons)))
			(car . (val . (prim . car)))
			(cdr . (val . (prim . cdr)))
			(null? . (val . (prim . null?)))

			. ,empty-env))
#;
  (			(not . (val . (prim . not)))
			(equal? . (val . (prim . equal?)))
			(symbol? . (val . (prim . symbol?)))
			
			
			)
  
  (define evalo
    (case-lambda
      [(expr) (run1 (val) (evalo expr val))]
      [(expr val) (evalo expr initial-env val)]
      [(expr env val)
       (trace-goal testing (trace-conde
	 [quote (evalo-quote expr env val)]
	 [literal (constrain (conde [(numbero expr)] [(booleano expr)])) (== expr val)]
	 [lookup (symbolo expr) (lookupo expr env val)]
	 [lambda (evalo-lambda expr env val)]
	 [apply (evalo-apply expr env val)]))]))

  (define (evalo-env expr env)
    ;; Forward direction evalo of expr in env not containing initial-env.
    (run1 (val) (evalo expr env val)))
  
  (define (evalo-quote expr env val)
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

  (define (evalo-lambda expr env val)
    (fresh ()
      (matcho ([expr ('lambda args body)]) ;TODO enable environment variables in patterns with unquote
	      ;(printfo "eval lambda~%")
	      (== `(closure (lambda ,args ,body) ,env) val)
	      (constrain
	       (conde
		 [(symbolo args)]
		 [(for-eacho (lambda (x) (symbolo x)) args)])))
      (not-in-envo 'lambda env)))

  (define (evalo-apply expr env val)
    (matcho
     ([expr (rator . rands)])
     (exist (closure args) ;TODO can we use first order matcho to eliminate need for exist?
	    (evalo rator env closure)
	    (conde
	      [(matcho
		 ([closure ('closure ('lambda params body) env^)])
		 (conde
		   [(symbolo params)
		    (exist (arg)
			   (evalo-listo rands env arg)
			   (evalo body `((,params . (val . ,arg)) . ,env^) val))]
		   [(pairo params)
		    (extend-env params rands env env
				(lambda (env^) (evalo body env^ val)))]))]
	      [(matcho ([closure ('prim . prim-id)])
		       (evalo-prim prim-id args val)
		       (evalo-listo rands env args))]))))
  
  (define (evalo-prim expr args val)
    (conde
      
      #;
      [(matcho ([expr (and . e*)])
	       (not-in-envo 'and env)
	       (evalo-and e* env val))]
      [(== expr 'cons) (matcho ([args (a d)]
				[val (a . d)]))]
      [(== expr 'car) (matcho ([args ((a . d))])
			      (== val a))]
      [(== expr 'cdr) (matcho ([args ((a . d))])
			      (== val d))]
      [(== expr 'null?)

       (disj (conj (=/= args '(())) (== val #f))
			      (conj (== args '(())) (== val #t)))]))

  (define (evalo-and e* env val)
    (conde
      [(== e* '()) (== val #t)]))

  (define (not-in-envo sym env)
    (noto (asspo sym env (lambda (v) succeed))))

  (define (extend-env params rands env env^ ctn)
    (conde
      [(== params '()) (== rands '()) (ctn env^)]
      [(matcho ([params (p . ps)]
		[rands (r . rs)])
	       ;(printfo "extend env~%")
	       (exist (arg)
		      (evalo r env arg)
		      (extend-env ps rs env `((,p . (val . ,arg)) . ,env^) ctn)))]))
  
  (define (evalo-listo expr env val)
    (conde
      [(== expr '()) (== val '())]
      [(matcho ([expr (e . es)]
		[val (v . vs)])
	       ;(printfo "eval listo~%")
	       (evalo e env v)
	       (evalo-listo es env vs))]))
)
