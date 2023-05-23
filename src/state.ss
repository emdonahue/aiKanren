(library (state)
  (export reify instantiate-var walk state-add-constraint print-substitution get-constraints remove-constraints) ;;TODO double check state exports
  (import (chezscheme) (prefix (substitution) substitution:) (values) (constraint-store) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let* ([v (substitution:walk (state-substitution s) v)]
	     [v (reify-constraint (state-constraints s) v)])
	(if (var? v) v (reify s v)))]
     [else v]))

  (define (state-add-constraint s v c)
    (assert (and (state? s) (var? v) (goal? c)))
    (set-state-constraints s (add-constraint (state-constraints s) v c)))

  (define (walk s v)
    (substitution:walk (state-substitution s) v))

  (define (get-constraints s vs)
    (fold-left normalized-conj* succeed (map (lambda (v) (get-constraint (state-constraints s) v)) vs)))

  (define (remove-constraints s vs)
    (set-state-constraints s (fold-left (lambda (s v) (remove-constraint s v)) (state-constraints s) vs)))
  
  (define (print-substitution s)
    (substitution:print-substitution (state-substitution s))))
