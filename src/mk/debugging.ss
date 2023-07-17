(library (debugging)
  (export printfo displayo noopo
	  print-substitution print-reification
	  trace-goals trace-goal-path)
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

  (define (walk-substitution s)
    (cert (state? s))
    (org-untrace (map (lambda (v) (walk s v)) (reverse (sbral->list (state-substitution s)))))))
