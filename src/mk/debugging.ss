(library (debugging)
  (export printfo displayo noopo
	  print-substitution print-reification
	  trace-goal-path trace-query run-trace-goal print-depth-limit trace-goal trace-conde
	  close-proof print-proof)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  ;; === DEBUG PRINTING ===
  
  (define (printfo . args)
    (noopo (apply org-printf args)))

  (define-syntax displayo
    (syntax-rules ()
      [(_ expr ...)
       (noopo (org-display expr ...))]))

  (define (noopo . args)
    succeed)

  ;; === PRETTY PRINTING ===
  
  (define (print-substitution s)
    (for-each org-print-item (map fx1+ (enumerate s)) s))

  (define (print-store s)
    3)
  
  (define (print-reification s)
    3)

  ;; === TRACING ===

  (define trace-path (make-parameter '(()))) ; Path taken so far through trace goals
  (define trace-goal-path (make-parameter '())) ; Prefix that trace-path must follow. Paths off prefix fail. Used to constrain search for debugging.
  (define trace-query (make-parameter #f))

  (define-syntax trace-goal ;TODO make goal-cond automatically add a condition for trace goals when not compiling and make trace goals vanish when compiling (test (optimize-level) param?
    (syntax-rules ()
      [(_ name goals ...)
       (make-trace-goal 'name '(goals ...) (conj* goals ...))]))
  
  (define-syntax trace-conde
    (syntax-rules ()
      [(_ (name g ...))
       (trace-goal name g ...)]
      [(_ c0 c ...) (conde-disj (trace-conde c0) (trace-conde c ...))]))
  
  (define (trace-path-cons name path)
    (if (or (null? path) (not (pair? (car path))))
	(cons name path)
	(cons (trace-path-cons name (car path)) (cdr path))))

  (define (run-trace-goal g s depth proof theorem ctn)
    (cert (goal? g) (state? s))
    (if (and theorem (theorem-contradiction theorem (trace-goal-name g)))
	(ctn fail s proof theorem)
	(begin
	  (org-print-header (trace-goal-name g))
	  (parameterize ([org-depth (fx1+ (org-depth))]
			 [trace-path (trace-path-cons (trace-goal-name g) (trace-path))])
	    (let ([proof (open-subproof proof (trace-goal-name g))])
	      (print-trace-body g s proof)
	      (let-values ([(answers p) (ctn (trace-goal-goal g) s proof (and theorem (subtheorem theorem)))])
		(org-print-header " <answers>")
		(org-print-item answers)
		(values (map (lambda (a) (cons (close-subproof (car a)) (cdr a))) answers) p)))))))
  
  (define (print-trace-body g s proof)
    (when (org-tracing)
	(org-print-header " <proof>")
	(org-print-item (print-proof proof))
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

  (define cursor '__)
  (define (cursor? c) (eq? c cursor))
  
  (define (open-subproof proof name)
    (if (cursor? (car proof)) (cons (list cursor name) (cdr proof))
	(cons (open-subproof (car proof) name) (cdr proof))))

  (define (close-subproof proof)
    (if (cursor? (caar proof)) (cons* cursor (cdar proof) (cdr proof))
	(cons (close-subproof (car proof)) (cdr proof))))

  (define close-proof cdr)
  
  (define (print-proof proof)
    (if (pair? proof) (reverse (map print-proof proof)) proof))

  (define (theorem-contradiction theorem term)
    (if (pair? theorem) (theorem-contradiction (car theorem) term) (not (or (eq? theorem cursor) (eq? theorem term)))))

  (define (subtheorem theorem)
    (if (pair? (car theorem)) (cons (subtheorem (car theorem)) (cdr theorem))
	(if (cursor? (car theorem)) theorem (cdr theorem))))
  
  (define (walk-substitution s)
    (cert (state? s))
    (org-untrace (map (lambda (v) (walk s v)) (reverse (sbral->list (state-substitution s)))))))
