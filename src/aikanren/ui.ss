(library (ui)
  (export run run* run1 run-states run*-states run1-states fresh conde constrain)
  (import (chezscheme) (running) (datatypes))

  (define-syntax conde ;TODO make conde expand syntactically
    (syntax-rules ()
      [(_ (g ...) ...)
       (disj* (conj* g ...) ...)]))
  
 (define-syntax fresh
   (syntax-rules ()
     [(_ () g) g] ; No reason to suspend if not creating new vars, since computation will be finite.
     [(_ () g0 g ...) (make-conj g0 (fresh () g ...))] 
     [(_ (q ...) g ...)
      (lambda (state p)
	(fresh-vars
	 (state-varid state) varid (q ...)
	 (values (fresh () g ...) (set-state-varid state varid) p)))]))

 (define-syntax runner
    (syntax-rules ()
      [(_ () g ...)
       (top-level-runner empty-state '() (fresh () g ...))]
      [(_ (q) g ...)
       (fresh-vars
	(state-varid empty-state) varid (q)
	(top-level-runner (set-state-varid empty-state varid) q (fresh () g ...)))]
      [(_ (q0 q ...) g ...)
       (fresh-vars
	(state-varid empty-state) varid (q0 q ...)
	(top-level-runner (set-state-varid empty-state varid) (list q0 q ...) (fresh () g ...)))]))
  
  (define-syntax run
    (syntax-rules ()
      ((_ n (q ...) g ...)
       (map car (runner-take n (runner (q ...) g ...))))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q ...) g ...) (run -1 (q ...) g ...))))
  
   (define-syntax run1
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run 1 (q ...) g ...)])
	 (if (null? ans) (void) (car ans))))))

   (define-syntax run-states
    (syntax-rules ()
      ((_ n (q ...) g ...)
       (map cdr (runner-take n (runner (q ...) g ...))))))

   (define-syntax run*-states
    (syntax-rules ()
      ((_ (q ...) g ...) (run-states -1 (q ...) g ...))))

   (define-syntax run1-states
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run-states 1 (q ...) g ...)])
	 (if (null? ans) failure (car ans))))))

   (define-syntax constrain
     (syntax-rules ()
       [(_ g ...) (make-constraint (fresh () g ...))]))
  
  ;; === UTILITIES ===

    (define-syntax fresh-vars
    (syntax-rules ()
      [(_ start-varid end-varid (q) body ...)
       (let ([q (make-var start-varid)]
		    [end-varid (fx1+ start-varid)])
	 body ...)]
      [(_ start-varid end-varid (q0 q ...) body ...)
       (let ([q0 (make-var start-varid)]
	     [intermediate-varid (fx1+ start-varid)])
	 (fresh-vars intermediate-varid end-varid (q ...) body ...))]))

    (define (top-level-runner state query conjuncts)
      (make-runner (make-bind conjuncts state) query empty-package)))
