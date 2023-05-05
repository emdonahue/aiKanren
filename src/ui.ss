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
       (runner-take
	n
	(run-goal
	 (fresh (q)
	   (lambda (s r)
	     (run-goal g0 s (make-runner 'dummy-stream q #f))))
	 empty-state
	 (make-runner 'top 'level 'runner)))
       )
      ))
  
  (define-syntax fresh
    (syntax-rules ()
      ((_ (x) g0)
       (lambda (s r)
	 (let-values ([(x s) (instantiate-var s)])
	   (set-runner-stream
	    r
	    (make-incomplete
	     g0 s)))))))
  
  #;
  (define-syntax fresh
    (syntax-rules ()
      [(_ (x) g0 g ...)
       (lambda (s)
	 (let-values ([(x s) (instantiate-var s)])
	   (bind* (run-goal g0 s) g ...)))])))
