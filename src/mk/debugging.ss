(library (debugging)
  (export printfo noopo
	  print-substitution print-reification
	  goal-trace goal-untrace)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  ;; === DEBUG PRINTING ===
  
  (define (printfo . args)
    (noopo (apply printf args)))

  (define (noopo . args)
    succeed)

  ;; === PRETTY PRINTING ===
  
  (define (print-substitution s)
    (assert (state? s))
    (org-untrace (map (lambda (p) (list (make-var (fx- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))

  (define (print-reification s)
    (assert (state? s))
    (org-untrace (map (lambda (var-val) (list (car var-val) (reify s (cadr var-val)))) (print-substitution s))))

  ;; === TRACING ===

  (define-syntax goal-trace (identifier-syntax org-trace))
  (define-syntax goal-untrace (identifier-syntax org-untrace))
  
)
