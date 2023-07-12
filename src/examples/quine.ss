(library (quine)
  (export evalo evalo-env)
  (import (chezscheme) (aikanren))
  
  (define evalo
    (case-lambda
      [(expr) (run1 (val) (evalo expr val))]
      [(expr val) (evalo expr '() val)]
      [(expr env val)
       (conde
	 [(eval-quote expr env val)]
	 [(symbolo expr) (lookupo expr env val)]
	 [(eval-lambda expr env val)]
	 [(eval-list expr env val)]
	 [(eval-apply expr env val)])]))

  (define (evalo-env expr env)
    ;; Forward direction evalo of expr in env not containing initial-env.
    (run1 (val) (evalo expr env val)))
  
  (define (eval-quote expr env val)
    (fresh ()
      (== `(quote ,val) expr)
      (absento 'closure val)
      (not-in-envo 'quote env)))
  
  (define (lookupo var env val) ;TODO can lookup be a constraint?
    (debug-goal 'lookupo (assoco var env val)))

  (define (eval-lambda expr env val)
    (fresh ()
      (matcho ([expr ('lambda (arg) body)]) ;TODO enable environment variables in patterns with unquote
	      (== `(closure ,arg ,body ,env) val)
	      (symbolo arg))
      (not-in-envo 'lambda env)))

  (define (eval-list expr env val)
    (matcho ([expr ('list . es)])
	    (eval-proper-list es env val)
	    (absento 'closure es)
	    (not-in-envo 'list env)))

  (define (eval-proper-list expr env val)
    (conde
      [(== expr '()) (== val '())]
      [(matcho ([expr (e . es)]
		[val (v . vs)])
	       (evalo e env v)
	       (eval-proper-list es env vs))]))
  
  (define (eval-apply expr env val)
    (matcho
     ([expr (rator . rands)])
     (matcho ([rands (rand)]) ;TODO merge optimized matchos
	     (exist (closure)
		    (evalo rator env closure)
		    (matcho
		     ([closure ('closure param body env^)])
		     (symbolo param)
		     (exist (arg)
			    (evalo rand env arg)			    
			    (evalo body `((,param . ,arg) . ,env^) val)))))))

  (define (not-in-envo sym env)
    (assert (symbol? sym))
    (noto (asspo sym env (lambda (v) succeed))))
  
  (define (eval-listo expr env val)
    (conde
      [(== expr '()) (== val '())]
      [(matcho ([expr (e . es)]
		[val (v . vs)])
	       (evalo e env v)
	       (eval-listo es env vs))]))
)
