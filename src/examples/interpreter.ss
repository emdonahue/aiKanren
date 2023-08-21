(library (interpreter) ; Ported from https://github.com/michaelballantyne/faster-minikanren/blob/master/full-interp.scm
  (export evalo initial-env evalo-env synthesizeo)
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
       (trace-conde
	[quote (evalo-quote expr env val)]
	[literal (constrain (conde [(numbero expr)] [(booleano expr)])) (== expr val)]
	[lookup (symbolo expr) (lookupo expr env val)]
	[lambda (evalo-lambda expr env val)]
	[apply (evalo-apply expr env val)]
	[letrec (evalo-letrec expr env val)]
	[if (evalo-if expr env val)]
	)]))

  (define synthesizeo
    ;; TODO quote/literal only needed if atoms in the output do not appear in the input
    (case-lambda
      [(examples)
       (run1 (body)
	     (exist (input output)
		    (absento 1 body)
		    ;(absento 2 body)
		    ;;(absento input body)
		    ;;(absento output body)
		    (fold-left (lambda (g io)
				 (conj g (evalo `(letrec ([f (lambda (x) ,body)])
						   (f ,(car io))) (cdr io)))) succeed examples)
		    ;;(fold-left (lambda (g io) (conj g (==> (== input (car io)) (== output (cdr io))))) succeed examples)
		    ;		  (fold-left (lambda (g io) (conj g (==> (== input (car io)) (== output (cdr io))))) succeed examples)
		    ;;(fold-left (lambda (g io) (disj g (== input (car io)))) fail examples)
		    ;(== input 1)
		    ;;(== input '(1 1))
		    ;;(== output '(1 . 1))
		    ;;(== args '(x y))
					;		  (== body '(cons x y))
		    ;;		  (fold-left (lambda (g io) (disj g (conj (== input (car io)) (== output (cdr io))))) fail examples)
		    ;;	  (== args '(y))
		    ;;		  (== body '(cons y y))
		    ))]))
  ;`(lambda ,(caar args-body) ,(cadr args-body))

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
	       [(== v `(val . ,val))]
	       [(matcho ([v ('rec . lambda-expr)])
			(== val `(closure ,lambda-expr ,env)))]))))

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
		   [(list-of-symbolso params)
		    (extend-env params rands env env
				(lambda (env^) (evalo body env^ val)))]))]
	      [(matcho ([closure ('prim . prim-id)])
		       (evalo-prim prim-id args val)
		       (displayo prim-id rands args val env)
		       (evalo-listo rands env args)
		       )])))) ;(trace-goal eval-prim-args (displayo prim-id rands args val env))

  (define (evalo-letrec expr env val)
    (matcho ([expr ('letrec ([name ('lambda args body)]) letrec-body)])
	    (disj (symbolo args) (list-of-symbolso args))
	    (not-in-envo 'letrec env)
	    (evalo letrec-body `((,name . (rec . (lambda ,args ,body))) . ,env) val)
	    ))
  
  (define (evalo-prim expr args val)
    (trace-conde
      
      #;
      [(matcho ([expr (and . e*)])
	       (not-in-envo 'and env)
	       (evalo-and e* env val))]
      [cons (== expr 'cons) (matcho ([args (a d)]
				[val (a . d)]))]
      [car (== expr 'car) (matcho ([args ((a . d))])
			      (== val a))]
      [cdr (== expr 'cdr) (matcho ([args ((a . d))])
			      (== val d))]
      [null (== expr 'null?) (disj (conj (=/= args '(())) (== val #f))
			      (conj (== args '(())) (== val #t)))]))

  (define (evalo-and e* env val)
    (conde
      [(== e* '()) (== val #t)]))

  (define (evalo-if expr env val)
    (matcho ([expr ('if c t f)])
	    (exist (tf)
		   (evalo c env tf)
		   (conde
		     [(== tf #f) (evalo f env val)]
		     [(=/= tf #f) (evalo t env val)]))))

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

  (define (list-of-symbolso xs)
    (disj (== xs '())
	  (matcho ([xs (a . d)])
		  (symbolo a)
		  (list-of-symbolso d))))
  
  (define (evalo-listo expr env val)
    (trace-goal proper-listo
     (conde
       [(== expr '()) (== val '())]
       [(matcho ([expr (e . es)]
		 [val (v . vs)])
					;(printfo "eval listo~%")
		(evalo e env v)
		(evalo-listo es env vs))])))
)
