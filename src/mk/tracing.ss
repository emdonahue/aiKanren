(library (tracing)
  (export trace-query trace-run-goal trace-goal trace-conde trace-proof-goals trace-goals
	  open-proof close-proof
	  trace-answer-proof trace-answer-state)
  (import (chezscheme) (datatypes) (solver) (utils) (state) (debugging))

  (define trace-query (make-parameter #f))
  (define trace-proof-goals (make-parameter #t))
  (define trace-goals (make-parameter #t))
  (define-structure (trace-answer theorem proof state))

  ;; === INTERFACE ===
  
  (define-syntax trace-goal ;TODO make goal-cond automatically add a condition for trace goals when not compiling and make trace goals vanish when compiling (test (optimize-level) param?
    (syntax-rules ()
      [(_ name goals ...)
       (if (trace-query)
	   (make-trace-goal 'name '(goals ...) (conj* goals ...))
	   (conj* goals ...))]))
  
  (define-syntax trace-conde
    (syntax-rules ()
      [(_ (name g ...))
       (trace-goal name g ...)]
      [(_ c0 c ...) (conde-disj (trace-conde c0) (trace-conde c ...))]))

  ;; === INTERPRETER ===

#;  
  (define (trace-run-goal g s p depth proof theorem) ;TODO make all goals accept a list of states so that we can print only the code as written and the input and output states without having to multiplex the code points for the tracing interpreter
    (cert (goal? g) (state-or-failure? s) (or (fail? g) (not (failure? s))) (package? p) (number? depth))
    (if (zero? depth) (begin (print-depth-limit) (values  '() p))
	(exclusive-cond
	 [(conj? g) (let-values ([(answers p) (trace-run-goal (conj-lhs g) s p depth proof theorem)])
		      (trace-bind (conj-rhs g) answers p depth))]
	 [(conde? g) (let*-values ([(lhs p) (trace-run-goal (conde-lhs g) s p depth proof theorem)]
				   [(rhs p) (trace-run-goal (conde-rhs g) s p depth proof theorem)])
		       (values (append lhs rhs) p))]
	 [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)]) ;TODO DRY the matcho/exist/fresh calls to common calling interface. maybe use => cond interface
			(trace-run-goal g s p (fx1- depth) proof theorem))]
	 [(exist? g) (let-values ([(g s p) ((exist-procedure g) s p)])
		       (trace-run-goal g s p depth proof theorem))]
	 [(fresh? g) (let-values ([(g s p) (g s p)])
		       (trace-run-goal g s p (fx1- depth) proof theorem))]
	 [(trace-goal? g) (run-trace-goal g s p depth proof theorem)]
	 [(proof-goal? g) (trace-run-goal (proof-goal-goal g) s p depth proof (proof-goal-proof g))]
	 [else (let ([s (run-constraint g s)])
		 (values (if (failure? s) '() (list (make-trace-answer theorem proof s))) p))])))
  #;
  (define (trace-bind g answers p depth)
    (cert (goal? g) (list? answers) (package? p) (number? depth))
    (if (null? answers) (values '() p)
	(let*-values ([(ans0 p) (trace-run-goal g (trace-answer-state (car answers)) p depth (trace-answer-proof (car answers)) (trace-answer-theorem (car answers)))]
		      [(ans^ p) (trace-bind g (cdr answers) p depth)])
	  (values (append ans0 ans^) p))))

  
  (define (trace-run-goal g s p n depth answers proof theorem ctn) ;TODO might be able to fold proofs into standard dfs with parameters and get rid of special cps trace interpreter
    (cond
     [(failure? s) (values n answers p)]
     [(succeed? g) (if (succeed? ctn)
		       (values (fx1- n) (cons (make-trace-answer theorem proof s) answers) p)
		       (trace-run-goal ctn s p n depth answers proof theorem succeed))]
     [(zero? depth) (print-depth-limit theorem) (values n answers p)]
     [(conj? g) (trace-run-goal (conj-lhs g) s p n depth answers proof theorem (conj (conj-rhs g) ctn))]
     [(conde? g) (let-values ([(num-remaining answers p) (trace-run-goal (conde-lhs g) s p n depth answers proof theorem ctn)])
		   (if (zero? num-remaining) (values num-remaining answers p)
		       (trace-run-goal (conde-rhs g) s p num-remaining depth answers proof theorem ctn)))]
     [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)])
		    (trace-run-goal g s p n (fx1- depth) answers proof theorem ctn))]
     [(exist? g) (let-values ([(g s p) ((exist-procedure g) s p)])
		   (trace-run-goal g s p n depth answers proof theorem ctn))]
     [(fresh? g) (let-values ([(g s p) (g s p)])
		   (trace-run-goal g s p n (fx1- depth) answers proof theorem ctn))]
     [(trace-goal? g) (cps-trace-goal g s p n depth answers proof theorem ctn)]
     [(untrace-goal? g)
      (if (theorem-contradiction theorem '())
	  (trace-run-goal fail s p n depth answers proof theorem ctn)
	  (trace-run-goal (untrace-goal-goal g) s p n depth answers (close-subproof proof) (subtheorem theorem) ctn))]
     [(proof-goal? g) (trace-run-goal (proof-goal-goal g) s p n depth answers proof (proof-goal-proof g) ctn)]
     [else (trace-run-goal ctn (run-constraint g s) p n depth answers proof theorem succeed)]))

  (define (cps-trace-goal g s p n depth answers proof theorem ctn)
    (if (theorem-contradiction theorem (trace-goal-name g))
	(trace-run-goal fail s p n depth answers proof theorem ctn)
	(let ([subgoal (trace-goal-goal g)]
	      [proof (open-subproof proof (trace-goal-name g))]
	      [subtheorem (subtheorem theorem)]
	      [ctn (make-untrace-goal ctn)])
	  (if (tracing? theorem)
	      (begin
		(org-print-header (trace-goal-name g))	   
		(parameterize ([org-depth (fx1+ (org-depth))])
		  (when (tracing? theorem) (print-trace-args g s proof))
		  (let*-values ([(ans-remaining answers p) (trace-run-goal subgoal s p n depth answers proof subtheorem ctn)])
		    (when (theorem-trivial? theorem)
		      (if (null? answers) (org-print-header "<failure>")
			  (begin (org-print-header "<answers>")
				 (for-each (lambda (i a)
					     (parameterize ([org-depth (fx1+ (org-depth))])
					       (org-print-header (number->string i))
					       (parameterize ([org-depth (fx1+ (org-depth))])
						 (print-trace-answer (trace-answer-proof a) (trace-answer-state a))))) (enumerate answers) answers))))
		    (values ans-remaining answers p))))
	      (trace-run-goal subgoal s p n depth answers proof subtheorem ctn)))))

;(not (theorem-trivial? theorem)) ; Do not print trace while constrained by a theorem to a single path, so that the trace starts at the unknown region.
;	(trace-run-goal (trace-goal-goal g) s p n depth answers (open-subproof proof (trace-goal-name g)) (subtheorem theorem) (make-untrace-goal ctn))
  
  ;; === PRINTING ===
#;  
  (define (run-trace-goal g s p depth proof theorem)
    (cert (goal? g) (state? s))
    (if (theorem-contradiction theorem (trace-goal-name g))
	(trace-run-goal fail s p depth proof theorem)
	(begin
	  (org-print-header (trace-goal-name g))
	  (parameterize ([org-depth (fx1+ (org-depth))])
	    (let ([proof (open-subproof proof (trace-goal-name g))])
	      (print-trace-body g s proof)
	      (let*-values ([(answers p) (trace-run-goal (trace-goal-goal g) s p depth proof (subtheorem theorem))]
			    [(answers) (remp (lambda (a) (theorem-contradiction (trace-answer-theorem a) '())) answers)])
		(org-print-header " <answers>")
		(org-print-item answers)
		(values (map (lambda (a)
			       (make-trace-answer
				(trace-answer-theorem a)
				(close-subproof (trace-answer-proof a))
				(trace-answer-state a))) answers) p)))))))
  
  (define (print-trace-args g s proof)
    (org-print-header "<arguments>")
    (parameterize ([org-depth (fx1+ (org-depth))])
      (print-trace-answer proof s)
      (print-trace-goal g)))

  (define (print-trace-goal g)
    (org-print-header "source")
    (for-each org-print-item (trace-goal-source g))
    (org-print-header "simplified")
    (org-print-item (trace-goal-goal g)))
  
  
  (define (print-trace-answer proof s)
    (org-print-header "proof")
    (org-print-item (reverse-proof proof))
    (org-print-header "query")
    (org-print-item (reify-var s (trace-query)))
    (let* ([substitution (walk-substitution s)] ;TODO print unbound variables in substitution debugging by checking var id in state
	   [constraints (filter (lambda (b) (and (goal? (cdr b)) (not (succeed? (cdr b))))) substitution)])
      (unless (null? constraints)
	(org-print-header "constraints")
	(for-each (lambda (b) (org-print-item (car b) (cdr b))) constraints))
      (unless (null? substitution)
	(org-print-header "substitution")
	(for-each (lambda (b) (org-print-item (car b) (cdr b))) substitution))))

  (define (print-depth-limit theorem)
    (when (tracing? theorem) (org-print-header " <depth limit reached>")))

  ;; === PROOFS ===
  
  (define cursor '__)
  (define (cursor? c) (eq? c cursor))

  (define open-proof (list cursor))
  
  (define (close-proof proof)
    (reverse-proof (cdr proof)))
  
  (define (open-subproof proof name)
    (if (cursor? (car proof)) (cons (list cursor name) (cdr proof))
	(cons (open-subproof (car proof) name) (cdr proof))))

  (define (close-subproof proof)
    (if (cursor? (caar proof)) (cons* cursor (cdar proof) (cdr proof))
	(cons (close-subproof (car proof)) (cdr proof))))
  
  (define (reverse-proof proof)
    (if (pair? proof) (reverse (map reverse-proof proof)) proof))

  (define (theorem-contradiction theorem term)
    (if (pair? theorem) (theorem-contradiction (car theorem) term) (not (or (eq? theorem cursor) (eq? theorem term)))))

  (define (subtheorem theorem)
    (if (pair? theorem)
	(if (pair? (car theorem)) (cons (subtheorem (car theorem)) (cdr theorem))
	    (if (cursor? (car theorem)) cursor (cdr theorem))) theorem))

  (define (tracing? theorem)
    (or (trace-proof-goals) (theorem-trivial? theorem)))

  (define (theorem-trivial? theorem)
    (if (pair? theorem) (theorem-trivial? (car theorem)) (cursor? theorem))))
