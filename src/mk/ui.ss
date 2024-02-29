(library (ui) ;TODO refactor this library into 'vars' and other
  (export run run* run1
	  run-states run*-states run1-state
	  run-dfs run*-dfs run**-dfs run1-dfs run1*-dfs
	  runner
	  fresh exist constraint conde
	  trace-run)
  (import (chezscheme) (running) (datatypes) (state) (utils) (tracing))
  
  (define-syntax fresh ; Introduce fresh variables.
    ;; (fresh (x y z) ...) 
    (syntax-rules ()
      [(_ () g0 g ...) (conj* g0 g ...)] ; No reason to suspend if not creating new vars, since computation will be finite.
      [(_ (q ...) g ...) ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
       (lambda (state p)
	 (fresh-vars
	  (state-varid state) varid (q ...)
	  (values (conj* g ...) (set-state-varid state varid) p)))]))

 (define-syntax conde ; Nondeterministic branching.
   
   (syntax-rules () ;TODO make conde do fail checks syntactically
     [(_ (g ...)) (conj* g ...)]
     [(_ c0 c ...)
      (conde-disj (conde c0) (conde c ...))]))
 
 (define-syntax exist ; Equivalent to fresh, but does not suspend search. Only creates fresh variables.
   (syntax-rules ()
     [(_ () g0 g ...) (conj* g0 g ...)]
     [(_ (q ...) g ...)
      (make-exist
       (lambda (state p)
	 (fresh-vars
	  (state-varid state) varid (q ...)
	  (values (conj* g ...) (set-state-varid state varid) p))))]))

 (define-syntax runner ; Returns a runner object that represents a lazy search. The stream can be advanced using runner-next to receive three values: the next complete answer, the state representing that answer, and another runner waiting to seek the next answer.
   ;; (runner (q ...) g ...)
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
  
 (define-syntax run ; Runs a standard interleaving search and returns the first n answers.
   ;; (run n (q ...) g ...)
    (syntax-rules ()
      [(_ n (q ...) g ...)
       (map car (runner-take n (runner (q ...) g ...)))]))


  
 (define-syntax run1 ; Returns the first answer
   ;; (run1 (q ...) g ...)
    (syntax-rules ()
      [(_ (q ...) g ...)
       (let ([ans (run 1 (q ...) g ...)])
	 (if (null? ans) (void) (car ans)))]))

   (define-syntax run-states ; Equivalent to run, but returns state objects for further processing.
    (syntax-rules ()
      [(_ n (q ...) g ...)
       (map cdr (runner-take n (runner (q ...) g ...)))]))

   (define-syntax run*-states ; Equivalent to run*, but returns state objects for further processing.
    (syntax-rules ()
      ((_ (q ...) g ...) (run-states -1 (q ...) g ...))))

   (define-syntax run1-state ; Equivalent to run1, but returns state objects for further processing.
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run-states 1 (q ...) g ...)])
	 (if (null? ans) failure (car ans))))))

   (define-syntax run-dfs ; Depth-first search based run equivalent. 
     ;; (run-dfs n depth (q ...) g ...)
     ;; Returns the first n answers, limited to a max search depth of depth.
     (syntax-rules ()
       [(_ n depth () g ...)
	(runner-dfs '() (conj* g ...) empty-state n depth)]
       [(_ n depth (q) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q)
	 (runner-dfs q (conj* g ...) (set-state-varid empty-state varid) n depth))]
       [(_ n depth (q ...) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q ...)
	 (runner-dfs (list q ...) (conj* g ...) (set-state-varid empty-state varid) n depth))]))

    (define-syntax run* ; Returns all answers using a depth-first search.
      (syntax-rules ()
	[(_ (q ...) g ...)
	 (run-dfs -1 -1 (q ...) g ...)]))
   
   (define-syntax run1-dfs ; Similar to run-dfs, but returns 1 answer.
     ;; (run-dfs depth (q ...) g ...)
     (syntax-rules ()
       [(_ depth (q ...) g ...)
	(let ([answers (run-dfs 1 depth (q ...) g ...)])
	  (if (null? answers) (void) (car answers)))]))

   (define-syntax run1*-dfs ; Similar to run-dfs, but returns one answer with infinite depth.
     (syntax-rules ()
       [(_ (q ...) g ...) (run1-dfs -1 (q ...) g ...)]))

   (define-syntax run*-dfs ; Similar to run-dfs, but returns all answers at given depth.
     (syntax-rules ()
       [(_ depth (q ...) g ...) (run-dfs -1 depth (q ...) g ...)]))

   (define-syntax run**-dfs ; Similar to run-dfs, but returns all answers with infinite depth.
     (syntax-rules ()
       [(_ (q ...) g ...) (run*-dfs -1 (q ...) g ...)]))

   (define-syntax trace-run ; Equivalent to run**-dfs or run*-dfs, but activates tracing system.
     ;; (trace-run (q) g ...)
     ;; (trace-run max-depth (q) g ...)
     ;; The tracing system prints nested debugging information including which trace-goals have been encountered, and various views of the substitution and constraints at each trace-goal. Output is formatted with line-initial asterisks, and is intended to be viewed in a collapsible outline viewer such as Emacs org mode.
     
     (syntax-rules ()
       [(_ (q ...) g ...) (trace-run -1 (q ...) g ...)]
       [(_ depth () g ...)
	(parameterize ([trace-query '()])
	  (trace-runner '() (conj* g ...) empty-state -1))]
       [(_ depth (q) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q)
	 (parameterize ([trace-query q])
	     (trace-runner q (conj* g ...) (set-state-varid empty-state varid) depth)))]
       [(_ depth (q ...) g ...)
	(fresh-vars
	 (state-varid empty-state) varid (q ...)
	 (parameterize ([trace-query (list q ...)])
	     (trace-runner (list q ...) (conj* g ...) (set-state-varid empty-state varid) depth)))]))

   (define-syntax constraint ; Wrapped goals are conjoined and interpreted as a constraint. 
     (syntax-rules ()
       [(_ g ...) (let ([c (conj* g ...)]) (if (or (fail? c) (succeed? c)) c (make-constraint c)))])) ;TODO try applying constraint immediately when applied
  
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
      (make-runner (make-suspended conjuncts state) query empty-package)))
