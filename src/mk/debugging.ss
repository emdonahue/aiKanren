(library (debugging)
  (export printfo noopo
	  print-substitution print-reification
	  goal-trace goal-untrace run-trace-goal)
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
    (org-untrace (map (lambda (var-val) (list (car var-val) (reify s (cadr var-val)))) (print-substitution s))))

  ;; === TRACING ===

  (define-syntax goal-trace (identifier-syntax org-trace))
  (define-syntax goal-untrace (identifier-syntax org-untrace))
  (define (run-trace-goal g return-labels ctn)
    (org-print-header (trace-goal-name g))
    (parameterize ([org-depth (fx1+ (org-depth))])
      (org-print-header "source")
      (for-each org-print-item (trace-goal-source g))
      (org-print-header "simplified")
      (org-print-item (trace-goal-goal g))
      (let ([ans (call-with-values ctn list)])
	(org-print-header "answers")
	(for-each (lambda (n v)
		    (org-print-item n v))
		  return-labels
		  ans)
	(apply values ans))))
  )
