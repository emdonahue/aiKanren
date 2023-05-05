(library (running)
  (export runner-next runner-step runner-null? runner-car runner-pair? runner-take)
  (import (chezscheme) (runner) (streams) (failure) (state))

  (define (runner-step r)
    (assert (runner? r))
    (stream-step (runner-stream r) r))
  
  (define (runner-null? r)
    (assert (runner? r))
    (failure? (runner-stream r)))
  
  (define (runner-pair? r)
    (assert (runner? r))
    (not (failure? (runner-car r))))
  
  (define (runner-car r)
    (assert (runner? r))
    (cond
     [(answer? (runner-stream r)) (runner-stream r)]
     [(complete? (runner-stream r)) (car (runner-stream r))]
     [else failure]))
  
  (define (runner-next r)
    (assert (runner? r))
    (let ([r (runner-step r)])
      (cond
       [(runner-null? r) (values (void) (void) r)]
       [(runner-pair? r) (values (reify (runner-car r) (runner-query r)) (runner-car r) r)]
       [else (runner-next r)])))
  
  (define (runner-take n r)
    (assert (runner? r))
    (if (zero? n) '()
	(let-values ([(reified state r) (runner-next r)])
	  (if (runner-null? r) '() (cons reified (runner-take (- n 1) r)))))))
