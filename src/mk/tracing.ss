(library (tracing)
  (export trace-query run-trace-goal trace-run-goal print-depth-limit trace-goal trace-conde
	  close-proof
	  trace-answer-proof trace-answer-state)
  (import (chezscheme) (datatypes) (solver) (utils) (state))

  (define trace-query (make-parameter #f))
  (define-structure (trace-answer theorem proof state))

  ;; === INTERFACE ===
  
  (define-syntax trace-goal ;TODO make goal-cond automatically add a condition for trace goals when not compiling and make trace goals vanish when compiling (test (optimize-level) param?
    (syntax-rules ()
      [(_ name goals ...)
       (make-trace-goal 'name '(goals ...) (conj* goals ...))]))
  
  (define-syntax trace-conde
    (syntax-rules ()
      [(_ (name g ...))
       (trace-goal name g ...)]
      [(_ c0 c ...) (conde-disj (trace-conde c0) (trace-conde c ...))]))

  ;; === INTERPRETER ===
  
  (define (trace-run-goal g s p depth proof theorem)
    (cert (goal? g) (state? s) (package? p) (number? depth))
    (if (zero? depth) (begin (print-depth-limit) (values  '() p))
	(exclusive-cond
	 [(conj? g) (let-values ([(answers p) (trace-run-goal (conj-lhs g) s p depth proof theorem)])
		      (trace-bind (conj-rhs g) answers p depth))]
	 [(conde? g) (let*-values ([(lhs p) (trace-run-goal (conde-lhs g) s p (if (conde? (conde-lhs g)) depth (fx1- depth)) proof theorem)]
				   [(rhs p) (trace-run-goal (conde-rhs g) s p (if (conde? (conde-rhs g)) depth (fx1- depth)) proof theorem)])
		       (values (append lhs rhs) p))]
	 [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)]) ;TODO DRY the matcho/exist/fresh calls to common calling interface. maybe use => cond interface
			(trace-run-goal g s p depth proof theorem))]
	 [(exist? g) (let-values ([(g s p) ((exist-procedure g) s p)])
		       (trace-run-goal g s p depth proof theorem))]
	 [(fresh? g) (let-values ([(g s p) (g s p)])
		       (trace-run-goal g s p depth proof theorem))]
	 [(trace-goal? g) (run-trace-goal g s p depth proof theorem)]
	 [(proof-goal? g) (trace-run-goal (proof-goal-goal g) s p depth proof (proof-goal-proof g))]
	 [else (values (let ([s (run-constraint g s)]) (if (failure? s) '() (list (make-trace-answer theorem proof s)))) p)])))
  
  (define (trace-bind g answers p depth)
    (cert (goal? g) (list? answers) (package? p) (number? depth))
    (if (null? answers) (values '() p)
	(let*-values ([(ans0 p) (trace-run-goal g (trace-answer-state (car answers)) p depth (trace-answer-proof (car answers)) (trace-answer-theorem (car answers)))]
		      [(ans^ p) (trace-bind g (cdr answers) p depth)])
	  (values (append ans0 ans^) p))))

  ;; === PRINTING ===
  
  (define (run-trace-goal g s p depth proof theorem)
    (cert (goal? g) (state? s))
    (if (theorem-contradiction theorem (trace-goal-name g))
	(trace-run-goal fail s p depth proof theorem)
	(begin
	  (org-print-header (trace-goal-name g))
	  (parameterize ([org-depth (fx1+ (org-depth))])
	    (let ([proof (open-subproof proof (trace-goal-name g))])
	      (print-trace-body g s proof)
	      (let-values ([(answers p)
			    (trace-run-goal (trace-goal-goal g) s p depth proof (subtheorem theorem))])
		(org-print-header " <answers>")
		(org-print-item answers)
		(values (map (lambda (a)
			       (make-trace-answer
				(trace-answer-theorem a)
				(close-subproof (trace-answer-proof a))
				(trace-answer-state a))) answers) p)))))))
  
  (define (print-trace-body g s proof)
    (when (org-tracing)
	(org-print-header " <proof>")
	(org-print-item (reverse-proof proof))
	(org-print-header " <source>")
	(for-each org-print-item (trace-goal-source g))
	(org-print-header " <simplified>")
	(org-print-item (trace-goal-goal g))
	(org-print-header " <query>")
	(org-print-item (reify-var s (trace-query)))
	#;
	(let ([substitution (walk-substitution s)])
	(org-print-header " <substitution>")
	(org-print-item (print-substitution substitution))
	(org-print-header " <constraints>")
	(org-print-item (print-store substitution))
	(org-print-header " <reification>")
	(org-print-item (print-reification substitution)))
	))

  (define (print-depth-limit)
    (org-print-header " <depth limit reached>"))

  ;; === PROOFS ===
  
  (define cursor '__)
  (define (cursor? c) (eq? c cursor))
  
  (define (open-subproof proof name)
    (if (cursor? (car proof)) (cons (list cursor name) (cdr proof))
	(cons (open-subproof (car proof) name) (cdr proof))))

  (define (close-subproof proof)
    (if (cursor? (caar proof)) (cons* cursor (cdar proof) (cdr proof))
	(cons (close-subproof (car proof)) (cdr proof))))

  (define (close-proof proof)
    (reverse-proof (cdr proof)))
  
  (define (reverse-proof proof)
    (if (pair? proof) (reverse (map reverse-proof proof)) proof))

  (define (theorem-contradiction theorem term)
    (if (pair? theorem) (theorem-contradiction (car theorem) term) (not (or (eq? theorem cursor) (eq? theorem term)))))

  (define (subtheorem theorem)
    (if (pair? (car theorem)) (cons (subtheorem (car theorem)) (cdr theorem))
	(if (cursor? (car theorem)) theorem (cdr theorem)))))
