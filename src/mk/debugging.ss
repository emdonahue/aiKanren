(library (debugging)
  (export printfo noopo
	  print-substitution print-reification
	  trace-goals run-trace-goal trace-goal-path)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  ;; === DEBUG PRINTING ===
  
  (define (printfo . args)
    (noopo (apply printf args)))

  (define (noopo . args)
    succeed)

  ;; === PRETTY PRINTING ===
  
  (define (print-substitution s)
    (cert (state? s))
    (org-untrace (map (lambda (p) (list (make-var (fx- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))

  (define (print-reification s)
    (cert (state? s))
    (org-untrace (reverse (map (lambda (var-val) (list (car var-val) (reify s (cadr var-val)))) (print-substitution s)))))

  ;; === TRACING ===

  (define trace-path (make-parameter '())) ; Path taken so far through trace goals
  (define trace-goal-path (make-parameter '())) ; Prefix that trace-path must follow. Paths off prefix fail. Used to constrain search for debugging.
  
  (define-syntax trace-goals (identifier-syntax org-trace))
  
  (define (run-trace-goal g s return-labels ctn)
    (if (and (not (null? (trace-goal-path))) (not (equal? (trace-goal-name g) (car (trace-goal-path)))))
	(ctn fail failure)
	(begin
	  (org-print-header (trace-goal-name g))
	  (parameterize ([org-depth (fx1+ (org-depth))]
			 [trace-path (cons (trace-goal-name g) (trace-path))])
	    (when (org-tracing)
	      (org-print-header " <path>")
	      (org-print-item (reverse (trace-path)))
	      (org-print-header " <source>")
	      (for-each org-print-item (trace-goal-source g))
	      (org-print-header " <simplified>")
	      (org-print-item (trace-goal-goal g))
	      (org-print-header " <substitution>")
	      (org-print-item (print-substitution s))
	      (org-print-header " <reification>")
	      (org-print-item (print-reification s)))
	    (let ([ans (call-with-values (lambda () (ctn g s)) list)])
	      (org-print-header " <answers>")
	      (for-each (lambda (n v)
			  (org-print-item n v))
			return-labels
			ans)
	      (apply values ans))))))
  )
