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

					;    (org-trace (display (run 1 (q) (evalo q q))))
;    (display (run 1 (q) (evalo q q)))
;(org-trace (display (run 1 (q) (evalo q q))))

    #;
    (display    (run 1 (q) (let* ([q^ q]
				  [quine (list q^ (list 'quote q^))])
    (evalo quine quine))))


(goal-trace    (display    (run1-dfs 20 (q) (let* ([q^ q]
					 [quine (list q^ (list 'quote q^))])
				    (evalo quine quine)))))
    
;    (goal-trace (run-dfs 1 5es0 (q) (evalo q '() q)))

    
    #;
    (tassert "evalo-quine quine" (run 5 (y) (evalo y y)) 1)

    
    ;;(display (run 1 (q) (evalo q '() q)))
    ))
