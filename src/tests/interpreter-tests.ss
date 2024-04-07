(import (test-runner) (mk) (mk interpreter) (utils))

(test-suite
 interpreter

 (tassert "evalo quote" (evalo '(quote 42)) 42)
 (tassert "evalo shadow quote" (evalo-env '(quote 42) '((quote . (val . 43)))) (void))
 
 (tassert "evalo true" (evalo #t) #t)
 (tassert "evalo false" (evalo #f) #f)
 (tassert "evalo number" (evalo 42) 42)

 (tassert "evalo lookup val" (evalo-env 'x '((x . (val . 42)))) 42)
 (tassert "evalo lookup val later" (evalo-env 'x '((y . (val . 43)) (x . (val . 42)))) 42)
 (tassert "evalo lookup val earlier" (evalo-env 'x '((x . (val . 42)) (y . (val . 43)))) 42)
 (tassert "evalo lambda single arg" (evalo-env '(lambda x x) '((x . (val . 42)))) `(closure x x ((x . (val . 42)))))
 (tassert "evalo lambda multi arg" (evalo-env '(lambda (x) x) '((x . (val . 42)))) `(closure (x) x ((x . (val . 42)))))

 (tassert "evalo cons" (evalo '(cons 42 43)) '(42 . 43))
 (tassert "evalo car" (evalo '(car (cons 42 43))) 42)
 (tassert "evalo cdr" (evalo '(cdr (cons 42 43))) 43)
 (tassert "evalo list" (evalo '(list 42 42)) '(42 42))

 (tassert "evalo null? number" (run1 () (evalo '(null? 42) #f)) '())
 (tassert "evalo null? empty" (evalo '(null? '())) #t)
 (tassert "evalo null? number" (run1 () (evalo '(null? (cons 42 43)) #f)) '())

 (tassert "evalo if true" (evalo '(if #t 1 2)) 1)
 (tassert "evalo if false" (evalo '(if #f 1 2)) 2)
 (tassert "evalo if null" (evalo '(if (null? '()) 1 2)) 1)
 (tassert "evalo if not null" (evalo '(if (null? (cons 3 4)) 1 2)) 2)
 
 (tassert "evalo apply lambda" (evalo '((lambda (x) x) 42)) 42)
 (tassert "evalo apply lambda eval arg" (evalo '((lambda (x) x) (cons 42 43))) '(42 . 43))
 (tassert "evalo apply lambda variadic" (evalo '((lambda x x) (cons 42 43))) '((42 . 43)))
 (tassert "evalo apply lambda variadic eval arg" (evalo '((lambda x x) (cons 42 43))) '((42 . 43)))
 (tassert "evalo apply var" (evalo-env '(x 42) `((x . (val . ,(evalo '(lambda (x) x)))))) 42)
 (tassert "evalo apply var variadic" (evalo-env '(x 42) `((x . (val . ,(evalo '(lambda x x)))))) '(42))   

 (tassert "evalo lambda list" (evalo '((lambda (x) (list x)) 42)) '(42))

 (tassert "evalo letrec" (evalo '(letrec ([x (lambda (y) (cons y y))]) x)) `(closure (y) (cons y y) ((x . (rec . ((y) (cons y y)))) . ,initial-env)))


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
 
 #;
 (begin
 


 (tassert "synthesize duplicate ground"
 (run1 body
 (absento 1 body)
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1))) '(cons x x))
 (tassert "synthesize duplicate" (synthesizeo '([1 . (1 . 1)])) '(cons x x))
 
 #;
 (parameterize ([trace-goals #t]
 [reify-constraints #f])
 (pretty-print (trace-run (body)
 (absento 1 body)
 #;
 (== body `(('(closure ;
 (lambda () (closure (lambda a '(1 . 1)) b)) ;
 c))))
 (evalo '(f 1) `((f . (rec . (lambda (x) ,body))) . ,initial-env) '(1 . 1)))))
 
 #;
 (display (trace-run (body)
 (absento '(1 . 1) body)
 (absento 1 body)
 (== body '(cons x x))
                ;(== body (list 'cons 'x vars)) ; ; ;
 ;;(== body `(cons . vars))
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1))))

 ;;8362 - disj that contains the bad match 8385  8383- disj should succeed but fails

 #;
 (display (trace-run (body)
 (prove ((letrec (apply (lookup) (literal) (apply (lookup) (prim) (proper-listo (lookup) (proper-listo (lookup) (proper-listo)))))))
 (absento '(1 . 1) body)
 (absento 1 body)
 ;;(== body '(cons x x))
 ;;(== body (list 'cons 'x vars))
 ;;(== body `(cons . vars))
 
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1)))))
 
                                        ;((letrec (apply (lookup) (literal) (apply (lookup) (prim) (lookup) (lookup) (eval-prim-args))))) ;

 #;
 (display (run 1 (body)
 (absento '(1 . 1) body)
 (absento 1 body)
 ;;(== body '(cons x x))
                                        ;(== body (list 'cons 'x vars)) ; ; ; ;
 ;;(== body `(cons . vars))
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1))))

 
 #;
 (run 1 (body)
 (absento '(1 . 1) body)
 ;;               (== body '(cons x x))
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1)))


 #;
 ((letrec (apply
 [lookup]
 [literal]
 [apply (lookup) (prim) (lookup) (lookup) (eval-prim-args)]))
 __)
 
 
 #;
 (parameterize ([reify-constraints #f])
 (pretty-print (run1 (body)
                     ;(absento '(1 . 1) body) ; ; ;
 (absento 1 body)
 (evalo '(f 1) `((f . (rec . (lambda (x) ,body))) . ,initial-env) '(1 . 1)))
 #;
 (evalo `(letrec ([f (lambda (x) ,body)]) ;
 (f 1)) '(1 . 1))))
 
 #;
 (tassert "evalo quine" (run 5 (y) (evalo y y)) 1)

 
 ;;(display (run 1 (q) (evalo q '() q)))

 ;;27719 - pconstraint should be rechecked but is normalized
 #;
 (org-trace    (display (run 1 (body)
 (absento '(1 . 1) body)
 (absento 1 body)
 ;;(== body '(cons x x))
 ;;(== body (list 'cons 'x vars))
 ;;(== body `(cons . vars))
 
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1)))))

 #;
 (display (run 1 (body)
 (absento 1 body)
 (evalo `(letrec ([f (lambda (x) ,body)])
 (f 1)) '(1 . 1))))
 
 )

 ;; Quines
#;
 (parameterize ([interpreter/number #f]
                [interpreter/boolean #f]
                [interpreter/lambda/variadic #f]
                [interpreter/lambda/multi-arg #f]
                [interpreter/if #f]
                [interpreter/letrec #f])

   (let ([q '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))])
    (tassert "evalo quine" (evalo q) q))
  
   (tassert "evalo quine" (run1 x1 (evalo x1 (list (assq 'list initial-env)) x1)) list?)
   (tassert "evalo 10 quine" (run 10 x1 (evalo x1 (list (assq 'list initial-env)) x1)) list?)
   (tassert "quine synthesis structure test" (run1 (q x) (evalo q q) (== q (list (list 'lambda (list x) (list 'list x (list 'list (list 'quote 'quote) x))) (list 'quote (list 'lambda (list x) (list 'list x (list 'list (list 'quote 'quote) x))))))) list?)

   (tassert "evalo twine" (run1 (x1 x2) (=/= x1 x2)
                                (evalo x1 (list (assq 'list initial-env)) x2)
                                (evalo x2 (list (assq 'list initial-env)) x1)) list?)

   (tassert "evalo thrine" (run1 (x1 x2 x3) (=/= x1 x2) (=/= x1 x3) (=/= x2 x3)
                                 (evalo x1 (list (assq 'list initial-env)) x2)
                                 (evalo x2 (list (assq 'list initial-env)) x3)
                                 (evalo x3 (list (assq 'list initial-env)) x1)) list?))

 ;; Synthesis
 (parameterize ([interpreter/number #f]
                [interpreter/boolean #f]
                [interpreter/lambda #f]
                [interpreter/letrec #f]
                [interpreter/quote #f]
                [max-depth 70])
(let ([env (filter (lambda (b) (memq (car b) '(null? cons car cdr))) initial-env)])
 (tassert "synthesize check environment injected append"
          (run1 q (evalo '(append x y) `((append . (rec . ((a b) (if (null? a) b (cons (car a) (append (cdr a) b)))))) (x . (val . (1 2))) (y . (val . (3))) . ,env) q)) '(1 2 3))

 (tassert "synthesize append ground"
          (run1 ()
                (synthesizeo '(if (null? a) b (cons (car a) (f (cdr a) b)))
                             '(
                               ((() (1)) . (1))
                               (((1) (2)) . (1 2))
                               )
                             env)) '())
 #;
 (tassert "synthesize append"
          (run1 (body)
;                (== body '(if (null? a) b (cons (car a) (f (cdr a) b))))
                (synthesizeo body
                             '(
                               ((() (1)) . (1))
                               (((1) (2)) . (1 2))
                               )
                             env)) 2))))
