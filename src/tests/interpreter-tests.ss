(library (interpreter-tests)
  (export run-interpreter-tests)
  (import (chezscheme) (test-runner) (aikanren) (interpreter) (utils))
  
  (define (run-interpreter-tests)
    
    (tassert "evalo quote" (evalo '(quote 42)) 42)
    (tassert "evalo shadow quote" (evalo-env '(quote 42) '((quote . (val . 43)))) (void))
;    (tassert "evalo true" (evalo #t) #t)
;    (tassert "evalo false" (evalo #f) #f)
;    (tassert "evalo number" (evalo 42) 42)

    (tassert "evalo lookup val" (evalo-env 'x '((x . (val . 42)))) 42)

    (tassert "evalo cons" (evalo '(cons 42 43)) '(42 . 43))
    (tassert "evalo car" (evalo '(car (cons 42 43))) 42)
    (tassert "evalo cdr" (evalo '(cdr (cons 42 43))) 43)
;    (display    (trace-run (q) (evalo '(null? 42) q)))
    (tassert "evalo null? number" (evalo '(null? 42)) #f)
    (tassert "evalo null? empty" (evalo '(null? '())) #t)
    (tassert "evalo null? pair" (evalo '(null? (cons 42 43))) #f)

    (tassert "evalo if true" (evalo '(if #t 1 2)) 1)
    (tassert "evalo if false" (evalo '(if #f 1 2)) 2)
    (tassert "evalo if null" (evalo '(if (null? '()) 1 2)) 1)
    (tassert "evalo if not null" (evalo '(if (null? (cons 3 4)) 1 2)) 2)
    
    (tassert "evalo lambda single arg" (evalo-env '(lambda x x) '((x . (val . 42)))) `(closure (lambda x x) ((x . (val . 42)))))
    (tassert "evalo lambda multi arg" (evalo-env '(lambda (x) x) '((x . (val . 42)))) `(closure (lambda (x) x) ((x . (val . 42)))))

;    (tassert "evalo and" (evalo '(and)) #t)

    (tassert "evalo apply lambda" (evalo '((lambda (x) x) 42)) 42)
    (tassert "evalo apply lambda eval arg" (evalo '((lambda (x) x) (cons 42 43))) '(42 . 43))
    (tassert "evalo apply lambda variadic" (evalo '((lambda x x) (cons 42 43))) '((42 . 43)))
    (tassert "evalo apply lambda variadic eval arg" (evalo '((lambda x x) (cons 42 43))) '((42 . 43)))
    (tassert "evalo apply var" (evalo-env '(x 42) `((x . (val . ,(evalo '(lambda (x) x)))))) 42)
    (tassert "evalo apply var variadic" (evalo-env '(x 42) `((x . (val . ,(evalo '(lambda x x)))))) '(42))

    (tassert "evalo list" (evalo '(list 42 42)) '(42 42))

    (tassert "evalo lambda list" (evalo '((lambda (x) (list x)) 42)) '(42))

    (tassert "evalo letrec" (evalo '(letrec ([x (lambda (y) (cons y y))]) x)) `(closure (lambda (y) (cons y y)) ((x . (rec . (lambda (y) (cons y y)))) . ,initial-env)))

    (tassert "evalo append null"
	     (evalo '(letrec ([append (lambda (lhs rhs)
					(if (null? lhs) rhs
					    (cons (car lhs) (append (cdr lhs) rhs))))])
		       (append '() '()))) '())
    (tassert "evalo append lhs null"
	     (evalo '(letrec ([append (lambda (lhs rhs)
					(if (null? lhs) rhs
					    (cons (car lhs) (append (cdr lhs) rhs))))])
		       (append '() '(1 2)))) '(1 2))

    (tassert "evalo append recursive 1"
	     (evalo '(letrec ([append (lambda (lhs rhs)
					(if (null? lhs) rhs
					    (cons (car lhs) (append (cdr lhs) rhs))))])
		       (append '(1) '(2 3)))) '(1 2 3))

    (tassert "evalo append recursive"
	     (evalo '(letrec ([append (lambda (lhs rhs)
					(if (null? lhs) rhs
					    (cons (car lhs) (append (cdr lhs) rhs))))])
		       (append '(1 2 3) '(4 5 6)))) '(1 2 3 4 5 6))
    
    (let ([q '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))])
      (tassert "evalo quine" (evalo q) q))


#;
    (display (trace-run (body)
			(absento '(1 . 1) body)
			(absento 1 body)
		;;(== body '(cons x x))
		;(== body (list 'cons 'x vars))
		;;(== body `(cons . vars))
			(evalo `(letrec ([f (lambda (x) ,body)])
				  (f 1)) '(1 . 1))))

#;    
    (display (run 1 (body)
			(absento '(1 . 1) body)
			(absento 1 body)
		;;(== body '(cons x x))
		;(== body (list 'cons 'x vars))
		;;(== body `(cons . vars))
			(evalo `(letrec ([f (lambda (x) ,body)])
			  (f 1)) '(1 . 1))))

    
#;
     (run 1 (body)
	    (absento '(1 . 1) body)
	    ;;	       (== body '(cons x x))
	    (evalo `(letrec ([f (lambda (x) ,body)])
		      (f 1)) '(1 . 1)))


#;
    ((letrec (apply
          [lookup]
          [literal]
          [apply (lookup) (prim) (lookup) (lookup) (eval-prim-args)]))
  __)
    
;    (tassert "synthesize cons" (synthesizeo '([(1 1) . (1 . 1)])) 1)



    
    #;
    (tassert "evalo quine" (run 5 (y) (evalo y y)) 1)

    
    ;;(display (run 1 (q) (evalo q '() q)))
    ))
