(library (mk core variables)
  (export var make-var var? var-id set-var-id! var< vars->list __)
  (import (chezscheme) (mk core utils))

  (define-structure (var id)) ;TODO make the var tag a unique object to avoid unifying with a (var _) vector and confusing it for a real var
  (define var ; Accepts an integer var-id and creates a var struct. Mostly for internal use, or for dynamically generating miniKanren programs.
    make-var)
  
  (define (var< x y)
    (cert (var? x) (var? y))
    (fx< (var-id x) (var-id y)))

  ;; === QUANTIFICATION ===
  (define __ ; Wildcard logic variable that unifies with everything without changing substitution.
    (vector '__))
  
  (define-syntax vars->list ; Turns a syntactic list of variables into a reified Scheme list.
    (syntax-rules ()
      [(_ ()) '()]
      [(_ (q ...)) (list q ...)]
      [(_ q) q])))
