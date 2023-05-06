(library (ui)
  (export == conde run run* fresh runner runner-next runner-step runner-null? runner-take)
  (import (chezscheme) (streams) (state) (runner) (running) (goals) (package))

  (define (== x y)
    (make-unification x y))

  (define-syntax conde
    (syntax-rules ()
      [(_ (g ...) ...)
       (disj* (conj* g ...) ...)]))
  
 (define-syntax fresh
   (syntax-rules ()
     [(_ () g ...)
      (lambda (start-state p)
	(fresh-suspend p start-state g ...))]
     [(_ (q ...) g ...)
      (lambda (start-state p)
	(fresh-vars
	 start-state end-state (q ...)
	 (fresh-suspend p end-state g ...)))]))

  (define-syntax runner
    (syntax-rules ()
      [(_ () g ...)
       (top-level-runner empty-state '() g ...)]
      [(_ (q) g ...)
       (fresh-vars
	empty-state start-state (q)
	(top-level-runner start-state q g ...))]
      [(_ (q0 q ...) g ...)
       (fresh-vars
	empty-state start-state (q0 q ...)
	(top-level-runner start-state (list q0 q ...) g ...))]))
  
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
	 (fresh-vars intermediate-state end-state (q ...) body ...))]))

    (define (top-level-runner state query . conjuncts)
      (make-runner (make-incomplete (conj conjuncts) state) query empty-package))

    (define (fresh-suspend package state . conjuncts)
      (values (make-incomplete (conj conjuncts) state) package)))
