(library (quine)
  (export evalo evalo-env)
  (import (chezscheme) (aikanren) (utils))
  
  (define evalo
    (case-lambda
      [(expr) (run1 (val) (evalo expr val))]
      [(expr val) (evalo expr '() val)]
      [(expr env val)
       (trace-goal evalo
	(conde
	  [(eval-quote expr env val)]
	  [(trace-goal lookupo (symbolo expr) (lookupo expr env val))]
	  [(eval-lambda expr env val)]
	  [(eval-list expr env val)]
	  [(eval-apply expr env val)]))]))

  (define (evalo-env expr env)
    ;; Forward direction evalo of expr in env not containing initial-env.
    (run1 (val) (evalo expr env val)))
  
  (define (eval-quote expr env val)
    (trace-goal eval-quote
     (fresh ()
       (== `(quote ,val) expr)
       (absento 'closure val)
       (not-in-envo 'quote env))))
  
  (define (lookupo var env val) ;TODO can lookup be a constraint?
    (trace-goal lookupo-r (displayo env) (assoco var env val)))

  (define (eval-lambda expr env val)
    (trace-goal eval-lambda
     (fresh ()
       (matcho eval-lambda ([expr ('lambda (arg) body)]) ;TODO enable environment variables in patterns with unquote
	       (== `(closure ,arg ,body ,env) val)
	       (symbolo arg))
       (not-in-envo 'lambda env))))

  (define (eval-list expr env val)
    (trace-goal eval-list
		(matcho eval-list ([expr ('list . es)])
			(eval-proper-list es env val)
			(absento 'closure es)
			(not-in-envo 'list env))))

  (define (eval-proper-list expr env val)
    (trace-goal eval-proper-list
     (conde
       [(== expr '()) (== val '())]
       [(matcho eval-proper-list ([expr (e . es)]
		 [val (v . vs)])
;		(noopo (org-display expr val))
		(evalo e env v)
		(eval-proper-list es env vs))])))
  
  (define (eval-apply expr env val)
    (trace-goal eval-apply
     (matcho eval-rator
      ([expr (rator . rands)])
      (matcho eval-rands ([rands (rand)])		;TODO merge optimized matchos
	      (fresh (closure)
		     (trace-goal eval-rator (evalo rator env closure))
		     (matcho eval-closure
		      ([closure ('closure param body env^)])
		      (symbolo param)
		      (fresh (arg)
			     (trace-goal evalo-rand (evalo rand env arg))			    
			     (trace-goal evalo-body (evalo body `((,param . ,arg) . ,env^) val)))))))))

  (define (not-in-envo sym env)
    (cert (symbol? sym))    
    (trace-goal not-in-envo (noto (asspo sym env (lambda (v) succeed)))))
  
  (define (eval-listo expr env val)
    (trace-goal eval-listo
     (conde
       [(== expr '()) (== val '())]
       [(matcho eval-listo ([expr (e . es)]
		 [val (v . vs)])
		(evalo e env v)
		(eval-listo es env vs))])))
)
