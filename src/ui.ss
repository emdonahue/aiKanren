(library (ui)
  (export == conde run fresh runner runner-next runner-step runner-null? runner-take)
  (import (chezscheme) (streams) (state) (runner) (running) (goals))

  (define (== x y)
    (make-unification x y))

  (define (conde x y)
    (make-disj x y))
  
 (define-syntax fresh
   (syntax-rules ()
     [(_ () g ...)
      (lambda (start-state r)
	(set-runner-stream r (make-incomplete (conj* g ...) start-state)))]
     [(_ (q ...) g ...)
      (fresh ()
	(fresh-vars start-state end-state (q ...) (conj* g ...)))]))
 
  (define-syntax runner2
    (syntax-rules ()
      [(_ (q) g0 g ...)
       (run-goal
	 (fresh (q)
	   (lambda (s r)
	     (run-goal (conj* g0 g ...) s (make-runner 'dummy-stream q #f))))
	 empty-state
	 (make-runner 'dummy-stream 'top-level 'runner))]))

  (define-syntax runner
    (syntax-rules ()
      [(_ (q) g ...)
       (fresh-vars
	empty-state start-state (q)
	(make-runner (make-incomplete (conj* g ...) start-state) q 'table))]))
  
  (define-syntax run
    (syntax-rules ()
      ((_ n (q ...) g ...)
       (runner-take n (runner (q ...) g ...)))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q ...) g ...) (run -1 (q ...) g ...))))

  ;; === UTILITIES ===

    (define-syntax fresh-vars
    (syntax-rules ()
      [(_ start-state end-state (q) body ...)
       (let-values ([(q end-state) (instantiate-var start-state)])
	 body ...)]
      [(_ start-state end-state (q0 q ...) body ...)
       (let-values ([(q0 intermediate-state) (instantiate-var start-state)])
	 (fresh-vars intermediate-state end-state (q ...) body ...))])))
