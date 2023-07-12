(library (debugging)
  (export printfo noopo print-substitution print-reification print-reification)
  (import (chezscheme) (datatypes) (sbral) (state) (utils))

  (define (printfo . args)
    (noopo (apply printf args)))

  (define (noopo . args)
    succeed)

     ;; === DEBUGGING ===

  (define (print-substitution s)
    (assert (state? s))
    (org-untrace (map (lambda (p) (list (make-var (fx- (sbral-length (state-substitution s)) (car p))) (cdr p))) (sbral->alist (state-substitution s)))))

  (define (print-reification s)
    (assert (state? s))
    (org-untrace (map (lambda (var-val) (list (car var-val) (reify s (cadr var-val)))) (print-substitution s))))
  
)
