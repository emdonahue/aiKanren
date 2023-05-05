(library (ui)
  (export == conde run fresh runner runner-next runner-step runner-null? runner-take)
  (import (chezscheme) (streams) (state) (runner) (running) (goals))

  (define (== x y)
    (make-unification x y))

  (define (conde x y)
    (make-disj x y))

  (define-syntax runner
    (syntax-rules ()
      [(_ (q) g0 g ...)
       (run-goal
	 (fresh (q)
	   (lambda (s r)
	     (run-goal (conj* g0 g ...) s (make-runner 'dummy-stream q #f))))
	 empty-state
	 (make-runner 'dummy-stream 'top-level 'runner))]))
  
  (define-syntax run
    (syntax-rules ()
      ((_ n (q ...) g ...)
       (runner-take n (runner (q ...) g ...)))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q ...) g ...) (run -1 (q ...) g ...))))
  
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
