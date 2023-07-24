(library (running)
  (export runner-next runner-step runner-take runner-dfs trace-runner)
  (import (chezscheme) (goals) (failure) (state) (datatypes) (utils) (tracing))

  (define (runner-null? r)
    (cert (runner? r))
    (failure? (runner-stream r)))
  
  (define (runner-step r)
    (cert (runner? r))
    (if (answer? (runner-stream r)) (make-runner failure (runner-query r) (runner-package r))
     (let-values ([(s p) (stream-step (runner-stream r) (runner-package r))])
       (make-runner s (runner-query r) p))))
  
  (define (runner-pair? r)
    (cert (runner? r))
    (not (failure? (runner-car r))))
  
  (define (runner-car r)
    (cert (runner? r))
    (cond
     [(answer? (runner-stream r)) (runner-stream r)]
     [(answers? (runner-stream r)) (answers-car (runner-stream r))]
     [else failure]))
  
  (define (runner-next r)
    (cert (runner? r))
    (let ([r (runner-step r)])
      (cond
       [(runner-null? r) (values (void) failure r)]
       [(runner-pair? r) (values (reify (runner-car r) (runner-query r)) (runner-car r) r)]
       [else (runner-next r)])))
  
  (define (runner-take n r)
    (cert (runner? r))
    (if (zero? n) '()
	(let-values ([(reified state r) (runner-next r)])
	  (if (failure? state) '() (cons (cons reified state) (runner-take (fx1- n) r))))))

  (define (runner-dfs q g s n depth)
    (map (lambda (s) (reify s q))
	 (let-values ([(ans-remaining answers p) (run-goal-dfs g s empty-package n depth '() succeed)])
	   (reverse (if (fx< ans-remaining 0) answers (list-head answers (fx- n (max 0 ans-remaining))))))))

  (define (trace-runner q g s depth)
    (let-values ([(num-remaining answers p)
		  (parameterize ([org-tracing (trace-goals)]
				 [trace-query q])
		    (trace-run-goal g s empty-package -1 depth '() open-proof open-proof succeed))])
      (cert (list? answers))
      (map (lambda (ans) (list (reify (trace-answer-state ans) q) (close-proof (trace-answer-proof ans)) (trace-answer-state ans))) (reverse answers)))))
