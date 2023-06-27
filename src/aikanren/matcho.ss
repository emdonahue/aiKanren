;; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables ""
(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution) (ui))

  (define-syntax build-substitution
    (syntax-rules ()
      [(_) '()]
      [(_ (v p) b ...) (let ([s (build-substitution b ...)])
			 (if (failure? s) s (mini-unify s v (build-pattern p))))]))
  
  (define-syntax build-pattern
    ;; Turn a pattern match schema into a full scheme object for unification.
    (syntax-rules (quote)
      [(_ (quote q)) 'q]
      [(_ (h . t)) (cons (build-pattern h) (build-pattern t))]
      [(_ ()) '()]
      [(_ v) v]))

  (define-syntax (matcho bindings) ; TODO specialize matcho for constraints vs goal & let interpreter decide implementation. constraint never needs to make fresh vars, goal doesn't need to know which vars are free (just whether)

    (define extract-vars
      ;; Extracts unique logic variable identifiers from the aggregate patterns.
      (case-lambda
	[(pattern) (extract-vars pattern '())]
	[(pattern vs)
	 (if (pair? pattern) (extract-vars (car pattern) (extract-vars (cdr pattern) vs))
	     (syntax-case pattern (quote)
	       [(quote q) vs]
	       [v (identifier? #'v)
		  (if (memp (lambda (e) (bound-identifier=? e #'v)) vs) vs (cons #'v vs))]
	       [(h . t) (extract-vars #'h (extract-vars #'t vs))]
	       [a vs]))]))
    
    (syntax-case bindings ()
      [(_ ([out-var (p-car . p-cdr)] ...) body ...)
       (with-syntax ([(in-var ...) (extract-vars #'(p-car ... p-cdr ...))]) ; Get new identifiers from pattern bindings that may require fresh logic variables.
	 #`(lambda (state package)
	     (let ([in-var (make-var 0)] ...) ; Create blank dummy variables for each identifier.
	       (let ([substitution (build-substitution (out-var (p-car . p-cdr)) ...)]) ; Unify each external destructured variable with its pattern in a new empty substitution.
		 (if (failure? substitution) (values fail failure package)
		     (let ([in-var (mini-reify substitution in-var)] ...) ; Reify each fresh variable in the substitution to see if it is already bound by the pattern match with a ground term in the destructured external variable.
		       (values
			(make-matcho
			 (filter var? (list out-var ...)) ; External vars
			 (filter (lambda (var) (and (var? var) (zero? (var-id var)))) (list in-var ...)) ; Internal vars are those that are 0 prior to subsequent mutation to give them ids.
			 (fresh ()
			   (== out-var (mini-reify substitution out-var)) ... ; Generate unifications of each external variable with its reified pattern, which has extracted all possible ground information from both the external variable and the pattern itself due to the double reification.
			   body ...))
			(set-state-varid ; Set as many variable ids as needed for fresh variables that remain fresh and so must enter the larger search as unbound variables.
			 state (fold-left
				(lambda (id v)
				  (if (and (var? v) (fx= 0 (var-id v))) 
				      (begin (set-var-id! v id) (fx1+ id)) id))
				(state-varid state) (list in-var ...)))
			package)))))))])))


