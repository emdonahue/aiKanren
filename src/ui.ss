(library (ui)
  (export == conde run run* run1 fresh runner runner-next runner-step runner-take failure? =/= absento constrain)
  (import (chezscheme) (running) (datatypes))

  (define-syntax conde
    (syntax-rules ()
      [(_ (g ...) ...)
       (disj* (conj* g ...) ...)]))
  
 (define-syntax fresh
   (syntax-rules ()
     [(_ () g ...) (conj* g ...)] ; No reason to suspend if not creating new vars, since computation will be finite.
     [(_ (q ...) g ...)
      (lambda (start-state p)
	(fresh-vars
	 start-state end-state (q ...)
	 (values (make-incomplete (fresh () g ...) end-state) p)))]))

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
  
   (define-syntax run1
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run 1 (q ...) g ...)])
	 (if (null? ans) (void) (car ans))))))

   (define constrain make-constraint)
  
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
      (make-runner (make-incomplete (conj conjuncts) state) query empty-package)))
