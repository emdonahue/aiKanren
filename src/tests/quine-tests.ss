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
    (let ([q '((lambda (x) (list x (list 'quote x))) '(lambda (x) (list x (list 'quote x))))])
      (display (parameterize ([trace-goals #f]) (trace-run () (evalo q q)))))

    (trace-run (q) (prove ((evalo (eval-apply (eval-rator (evalo (eval-lambda (not-in-envo)))) (evalo-rand (evalo (eval-quote (not-in-envo)))) (evalo-body (evalo (eval-list (eval-proper-list (evalo (lookupo (lookupo-r))) (eval-proper-list (evalo (eval-list (eval-proper-list (evalo (eval-quote (not-in-envo))) (eval-proper-list (evalo (lookupo (lookupo-r))) (eval-proper-list))) (not-in-envo))) (eval-proper-list))) (not-in-envo)))))))
			  (evalo q q)))
    
    ;;((evalo (eval-apply (eval-rator (evalo (eval-lambda (not-in-envo)))) (evalo-rand (evalo (eval-quote (not-in-envo)))) (evalo-body (evalo (eval-list (eval-proper-list (evalo (lookupo (lookupo-r))) (eval-proper-list (evalo (eval-list (eval-proper-list (evalo (eval-quote (not-in-envo))) (eval-proper-list (evalo (lookupo (lookupo-r))) (eval-proper-list))) (not-in-envo))) (eval-proper-list))) (not-in-envo)))))))

    
    (exit)
(org-trace    (tassert "full quines run" (run1 (q) (evalo q q)) list?))

    (printf "DONE")
    (exit)
    (tassert "unconstrained quines correct structure" (run1 (q x) (evalo q q) (== q (list (list 'lambda (list x) (list 'list x (list 'list (list 'quote 'quote) x))) (list 'quote (list 'lambda (list x) (list 'list x (list 'list (list 'quote 'quote) x))))))) list?)))
