(library (ui) ;TODO refactor this library into 'vars' and other
  (export run run* run1
	  run-states run*-states run1-state
	  run-dfs run*-dfs run**-dfs run1-dfs run1*-dfs
	  fresh exist constrain
	  trace-run)
  (import (chezscheme) (running) (datatypes) (state) (utils))
  
 (define-syntax fresh ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
   (syntax-rules ()
     [(_ () g0 g ...) (conj* g0 g ...)] ; No reason to suspend if not creating new vars, since computation will be finite.
     [(_ (q ...) g ...)
      (lambda (state p)
	(fresh-vars
	 (state-varid state) varid (q ...)
	 (values (conj* g ...) (set-state-varid state varid) p)))]))

 (define-syntax exist
   (syntax-rules ()
     [(_ () g0 g ...) (conj* g0 g ...)]
     [(_ (q ...) g ...)
      (make-exist
       (lambda (state p)
	 (fresh-vars
	  (state-varid state) varid (q ...)
	  (values (conj* g ...) (set-state-varid state varid) p))))]))

 (define-syntax runner
    (syntax-rules ()
      [(_ () g ...)
       (top-level-runner empty-state '() (conj* g ...))]
      [(_ (q) g ...)
       (fresh-vars
	(state-varid empty-state) varid (q)
	(top-level-runner (set-state-varid empty-state varid) q (conj* g ...)))]
      [(_ (q0 q ...) g ...)
       (fresh-vars
	(state-varid empty-state) varid (q0 q ...)
	(top-level-runner (set-state-varid empty-state varid) (list q0 q ...) (conj* g ...)))]))
  
  (define-syntax run
    (syntax-rules ()
      [(_ n (q ...) g ...)
       (map car (runner-take n (runner (q ...) g ...)))]))

  (define-syntax run*
    (syntax-rules ()
      [(_ (q ...) g ...) (run -1 (q ...) g ...)]))
  
   (define-syntax run1
    (syntax-rules ()
      [(_ (q ...) g ...)
       (let ([ans (run 1 (q ...) g ...)])
	 (if (null? ans) (void) (car ans)))]))

   (define-syntax run-states
    (syntax-rules ()
      [(_ n (q ...) g ...)
       (map cdr (runner-take n (runner (q ...) g ...)))]))

   (define-syntax run*-states
    (syntax-rules ()
      ((_ (q ...) g ...) (run-states -1 (q ...) g ...))))

   (define-syntax run1-state 
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run-states 1 (q ...) g ...)])
	 (if (null? ans) failure (car ans))))))

   (define-syntax run-dfs
     (syntax-rules ()
       [(_ n depth () g ...)
	(runner-dfs '() (conj* g ...) (set-state-varid empty-state varid) n depth)]
       [(_ n depth (q) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q)
	 (runner-dfs q (conj* g ...) (set-state-varid empty-state varid) n depth))]
       [(_ n depth (q ...) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q ...)
	 (runner-dfs (list q ...) (conj* g ...) (set-state-varid empty-state varid) n depth))]))

   (define-syntax run1-dfs
     (syntax-rules ()
       [(_ depth (q ...) g ...)
	(let ([answers (run-dfs 1 depth (q ...) g ...)])
	  (if (null? answers) (void) (car answers)))]))

   (define-syntax run1*-dfs
     (syntax-rules ()
       [(_ (q ...) g ...) (run1-dfs -1 (q ...) g ...)]))

   (define-syntax run*-dfs
     (syntax-rules ()
       [(_ depth (q ...) g ...) (run-dfs -1 depth (q ...) g ...)]))

   (define-syntax run**-dfs
     (syntax-rules ()
       [(_ (q ...) g ...) (run*-dfs -1 (q ...) g ...)]))

   (define-syntax trace-run
     (syntax-rules ()
       [(_ (q ...) g ...) (trace-run -1 (q ...) g ...)]
       [(_ depth (q) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q)
	 (trace-runner q (conj* g ...) (set-state-varid empty-state varid) depth))]
       [(_ depth (q ...) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q ...)
	 (trace-runner (list q ...) (conj* g ...) (set-state-varid empty-state varid) depth))]))

   (define-syntax constrain
     (syntax-rules ()
       [(_ g ...) (constraint (conj* g ...))]))
  
  ;; === UTILITIES ===

   (define-syntax fresh-vars ;TODO make fresh-vars non-recursive ala matcho
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
