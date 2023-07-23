(library (debugging)
  (export printfo displayo noopo
	  print-substitution print-reification
	  walk-substitution)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  ;; === DEBUG PRINTING ===
  
  (define (printfo . args)
    (noopo (apply org-printf args)))

  (define-syntax displayo
    (syntax-rules ()
      [(_ expr ...)
       (noopo (org-display expr ...))]))

  (define-syntax noopo
    (syntax-rules ()
      [(_ body ...)
       (let ([noopo (lambda (s p) body ... (values succeed s p))]) noopo)]))

  ;; === PRETTY PRINTING ===
  
  (define (print-substitution s)
    (for-each org-print-item (map fx1+ (enumerate s)) s))

  (define (print-store s)
    3)
  
  (define (print-reification s)
    3)

  (define (walk-substitution s)
    (cert (state? s))
    (org-untrace (map (lambda (v) (walk s v)) (reverse (sbral->list (state-substitution s)))))))
