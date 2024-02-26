(library (debugging)
  (export printfo displayo noopo
	  print-substitution print-reification
	  walk-substitution)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  ;; === DEBUG PRINTING ===
  
  (define (printfo . args) ; A no-op goal that prints its arguments as part of the debug logging system.
    (noopo (apply org-printf args) (org-printf "~%")))

  (define-syntax displayo ; A no-op goal that reifies and displays its arguments as part of the debug logging system.
    (syntax-rules ()
      [(_ expr ...)
       (let ([displayo (lambda (s p) (org-display (reify s expr) ...) (values succeed s p))]) displayo)]))

  (define-syntax noopo ; A no-op goal that executes arbitrary code when called as part of the search.
    (syntax-rules ()
      [(_ body ...)
       (let ([noopo (lambda (s p) body ... (values succeed s p))]) noopo)]))

  ;; === PRETTY PRINTING ===
  
  (define (print-substitution s) ; Prints a human
    (for-each org-print-item (map fx1+ (enumerate s)) s))

  (define (walk-substitution s)
    (cert (state? s))
    (org-untrace
     (let ([bindings (reverse (sbral->list (state-substitution s)))])
       (map (lambda (i b) (cons (fx1+ i) b)) (enumerate bindings) bindings)))))
