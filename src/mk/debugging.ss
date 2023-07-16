(library (debugging)
  (export printfo displayo noopo
	  print-substitution print-reification
	  trace-goals run-trace-goal trace-goal-path)
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

  (define trace-path (make-parameter '())) ; Path taken so far through trace goals
  (define trace-goal-path (make-parameter '())) ; Prefix that trace-path must follow. Paths off prefix fail. Used to constrain search for debugging.
  
  (define-syntax trace-goals (identifier-syntax org-trace))
  
  (define (run-trace-goal g s return-labels ctn)
    (parameterize ([trace-path (cons (trace-goal-name g) (trace-path))])
     (cond
      [(null? (trace-goal-path))
       (org-print-header (trace-goal-name g))
       (parameterize ([org-depth (fx1+ (org-depth))])
	 (when (org-tracing)
	   (org-print-header " <path>")
	   (org-print-item (reverse (trace-path)))
	   (org-print-header " <source>")
	   (for-each org-print-item (trace-goal-source g))
	   (org-print-header " <simplified>")
	   (org-print-item (trace-goal-goal g))
	   (let ([substitution (walk-substitution s)])
	     (org-print-header " <substitution>")
	     (org-print-item (print-substitution substitution))
	     (org-print-header " <constraints>")
	     (org-print-item (print-store substitution))
	     (org-print-header " <reification>")
	     (org-print-item (print-reification substitution)))
	   )
	 (let ([ans (call-with-values (lambda () (ctn (trace-goal-goal g) s)) list)])
	   (org-print-header " <answers>")
	   (for-each (lambda (n v)
		       (org-print-item n v))
		     return-labels
		     ans)
	   (apply values ans)))]
      [(equal? (trace-goal-name g) (car (trace-goal-path)))
       (parameterize ([trace-goal-path (cdr (trace-goal-path))]) (ctn (trace-goal-goal g) s))]
      [else (ctn fail failure)])))

  (define (walk-substitution s)
    (cert (state? s))
    (org-untrace (map (lambda (v) (walk s v)) (reverse (sbral->list (state-substitution s)))))))
