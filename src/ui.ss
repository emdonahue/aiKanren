(library (ui)
  (export == conde run fresh)
  (import (chezscheme) (streams) (state) (runner))

  (define (== x y)
    (make-unification x y))

  (define (conde x y)
    (make-disj x y))

  (define-syntax run
    (syntax-rules ()
      ((_ n (q) g0)
       (make-runner 1 2 3)
       )
      ))
  
  (define-syntax fresh
    (syntax-rules ()
      ((_ (x) g0)
       (lambda (s)
	 (let-values ([(x s) (instantiate-var s)])
	   (run-goal g0 s))))))
  
  #;
  (define-syntax fresh
    (syntax-rules ()
      [(_ (x) g0 g ...)
       (lambda (s)
	 (let-values ([(x s) (instantiate-var s)])
	   (bind* (run-goal g0 s) g ...)))])))
