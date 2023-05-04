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
	     (run-goal
	      g0
	      s
	      (make-runner #t q #f))))
	 empty-state
	 (make-runner #f #f #f)))
       )
      ))
  
  (define-syntax fresh
    (syntax-rules ()
      ((_ (x) g0)
       (lambda (s r)
	 (let-values ([(x s) (instantiate-var s)])
	   (set-runner-stream
	    r
	    (make-suspended
	     g0 s)))))))
  
  #;
  (define-syntax fresh
    (syntax-rules ()
      [(_ (x) g0 g ...)
       (lambda (s)
	 (let-values ([(x s) (instantiate-var s)])
	   (bind* (run-goal g0 s) g ...)))])))
