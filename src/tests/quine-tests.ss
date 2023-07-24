(library (quine-tests)
  (export run-quine-tests)
  (import (chezscheme) (test-runner) (aikanren) (quine) (utils) (debugging))
  
  (define (run-quine-tests)

    (tassert "evalo-quine quote" (evalo '(quote 42)) 42)
    (tassert "evalo-quine shadow quote" (evalo-env '(quote 42) '((quote . (val . 43)))) (void))

    (tassert "evalo-quine lookup val" (evalo-env 'x '((x . 42))) 42)

    (tassert "evalo-quine list empty" (evalo '(list)) '())
    (tassert "evalo-quine list" (evalo '(list '42 '42)) '(42 42))
    
    (tassert "evalo-quine lambda" (evalo-env '(lambda (x) x) '((x . 42))) `(closure x x ((x . 42))))


    (tassert "evalo-quine apply lambda" (evalo '((lambda (x) x) (quote 42))) 42)
    (tassert "evalo-quine apply var" (evalo-env '(x '42) `((x . ,(evalo '(lambda (x) x))))) 42)

    (tassert "evalo-quine lambda list" (evalo '((lambda (x) (list x)) '42)) '(42))

    (let ([q '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))])
      (tassert "evalo-quine quine" (evalo q) q))

    #;
    (parameterize ([trace-goal-print #t])
    (trace-run 10 (q) (prove ((evalo
			   (eval-apply
			    (eval-rator (evalo __))))) (evalo q q))))
    
    ;;prints quine proof
  #;
    (pretty-print (cadar (let ([quine '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))])
    (trace-run (q) (== q quine) (evalo q q)))))

#;
    (parameterize ([trace-goals #t]
		   [trace-proof-goals #t])
(display (trace-run (q) (prove ((evalo
			      (eval-apply
			       (eval-rator (evalo (eval-lambda (not-in-envo))))
			       (evalo-rand (evalo (eval-quote (not-in-envo))))
			       (evalo-body
				(evalo
				 (eval-list
				  (eval-proper-list
				   (evalo (lookupo (lookupo-r)))
				   (eval-proper-list
				    (evalo
				     (eval-list
				      (eval-proper-list
				       (evalo (eval-quote (not-in-envo)))
				       (eval-proper-list
					(evalo (lookupo (lookupo-r)))
					(eval-proper-list)))
				      (not-in-envo)))
				    (eval-proper-list)))
				  (not-in-envo)))))))
			    (evalo q q)))))

    #;
((evalo
   (eval-apply
     (eval-rator (evalo (eval-lambda (not-in-envo))))
     (evalo-rand (evalo (eval-quote (not-in-envo))))
     (evalo-body
       (evalo
         (eval-list
           (eval-proper-list
             (evalo (lookupo (lookupo-r)))
             (eval-proper-list
               (evalo
                 (eval-list
                   (eval-proper-list
                     (evalo (eval-quote (not-in-envo)))
                     (eval-proper-list
                       (evalo (lookupo (lookupo-r)))
                       (eval-proper-list)))
                   (not-in-envo)))
               (eval-proper-list)))
           (not-in-envo)))))))

    #;
(prove ((evalo
				(eval-apply
				 (eval-rator (evalo (eval-lambda (not-in-envo))))
				 (evalo-rand (evalo (eval-quote (not-in-envo))))
				 (evalo-body
				  (evalo
				   (eval-list
				    (eval-proper-list (evalo (lookupo (lookupo-r __))))))))))
			    (evalo q q))

    #;
    (trace-run (x1 x2) (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)])
	       (trace-conde [x2=1 (== x2 1)] [x2=2 (== x2 2)]))

					;    (org-trace (display (run 1 (q) (evalo q q))))
;    (display (run 1 (q) (evalo q q)))
;(org-trace (display (run 1 (q) (evalo q q))))

    #;
    (display    (run 1 (q) (let* ([q^ q]
				  [quine (list q^ (list 'quote q^))])
    (evalo quine quine))))

#;
    (display    (run1 (q) (let* ([q^ `(lambda (x) ,q)]
					[quine (list q^ (list 'quote q^))])
				   (evalo quine quine))))

#;
    (trace-goals
     (parameterize ([trace-goal-path
		     '(evalo eval-apply eval-rator evalo eval-lambda not-in-envo
 evalo-rand evalo eval-quote not-in-envo evalo-body evalo
 eval-list eval-proper-list evalo lookupo lookupo-r
 eval-proper-list evalo eval-list eval-proper-list evalo
 eval-quote not-in-envo eval-proper-list evalo lookupo
 lookupo-r eval-proper-list not-in-envo)

		     
		     ])
		   (run-dfs 1 28 (q) (evalo q '() q))))

;    (trace-run 2 (q) (evalo q q))

					;    (evalo (eval-apply (eval-rator lookupo) (eval-rand)))

;    (display    (trace-run (x1) (trace-conde [path1 (== x1 1)] [path2 (== x1 2)])))

    
    #;
    (parameterize ([trace-goal-path '(evalo eval-apply eval-rator evalo eval-lambda not-in-envo evalo-rand evalo)])
      (display (run-dfs 1 25 (q) (evalo q '() q))))
    
    
    #;
    (tassert "evalo-quine quine" (run 5 (y) (evalo y y)) 1)

    
    ;(display (run 1 (q) (evalo q '() q)))
    ))
