;TODO first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable
(library (matcho) ; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables"
					
  (export matcho matcho-pair)
  (import (chezscheme) (datatypes) (mini-substitution) (ui) (state))
  
  (define-syntax build-substitution
    ;; Walks each out-variable in turn and unifies it with its pattern, failing the entire computation if any pattern unification fails before walking subsequent variables.
    (syntax-rules ()
      [(_ state package substitution grounding ((out-var pattern)) body ...)
       (let* ([out-var (if (null? grounding) (walk-var state out-var) (car grounding))] ;TODO integrate constraint substitutions with matcho
	      [grounding (if (null? grounding) grounding (cdr grounding))]
	      [substitution (mini-unify substitution (build-pattern pattern) out-var)])
	 (if (failure? substitution)
	     (values #f fail failure package)
	     (begin body ...)))]
      [(_ state package substitution grounding (binding bindings ...) body ...)
       (build-substitution state package substitution grounding (binding)
			   (build-substitution state package substitution grounding (bindings ...) body ...))]))
  
  (define-syntax build-pattern
    ;; Turn a pattern match schema into a full scheme object for unification.
    (syntax-rules (quote)
      [(_ (quote q)) 'q]
      [(_ (h . t)) (cons (build-pattern h) (build-pattern t))]
      [(_ ()) '()]
      [(_ v) v]))

  (define-syntax matcho-pair ;TODO generalize matcho-pair to multiple pairs, pairs with constant patterns, and other common patterns such as a-list
    ;; Optimization to inline the destructuring of a single generic pair.
    (syntax-rules () ;TODO specialize multiple pair matcho-pair on different modes (ground, free, etc) so we can always instantly destructure whatever is ground. may involve further manipulations of goal order based on mode
      [(_ ([out-var (p-car . p-cdr)]) body ...) ;TODO can we make a generalized matcho out of matcho-pair on each pair of a pattern?
       (exclusive-cond
	[(var? out-var)
	 (make-matcho
	  (list out-var)
	  '()
	  (lambda (state package grounding)
	    (let ([out-var (if (null? grounding) (walk-var state out-var) (car grounding))])
	      (exclusive-cond
	       [(pair? out-var)
		(values #t
			(let ([p-car (car out-var)]
			      [p-cdr (cdr out-var)])
			  (conj* body ...))
			state package)]
	       [(var? out-var)
		(values
		 #f
		 (let ([p-car (make-var (state-varid state))]
		       [p-cdr (make-var (fx1+ (state-varid state)))])
		   (conj* (== out-var (cons p-car p-cdr)) body ...))
		 (if (var? out-var) (set-state-varid state (fx+ 2 (state-varid state))) state)
		 package)]
	       [else (values #t fail failure package)]))))]
	[(pair? out-var) ; If the term is ground, just destructure it and continue.
	 (let ([p-car (car out-var)]
	       [p-cdr (cdr out-var)])
	   (conj* body ...))]
	[else fail])]))
  
  (define-syntax (matcho bindings) ; TODO specialize matcho for constraints vs goal & let interpreter decide implementation. constraint never needs to make fresh vars, goal doesn't need to know which vars are free (just whether)
    ;; TODO can we fire matcho immediately if its structural recursion instead of waiting on a conjunct ahead of it that may be all free? reordering conjuncts

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
      [(_ ([out-var (p-car . p-cdr)]) body ...)
       (and (identifier? #'p-car) (identifier? #'p-cdr))
       #'(matcho-pair ([out-var (p-car . p-cdr)]) body ...)]
      [(_ ([out-var (p-car . p-cdr)] ...) body ...) ;TODO add fender to matcho to prevent duplicate lhs vars
       (with-syntax ([(in-var ...) (extract-vars #'(p-car ... p-cdr ...))]) ; Get new identifiers from pattern bindings that may require fresh logic variables.
	 #`(normalize-matcho
	    (list out-var ...) ;TODO equip matcho with the patterns externally to fail constraints without invoking goal. 
	    '()
	    (lambda (state package grounding)
	      (let ([substitution '()]
		    [grounding (reverse grounding)]
		    [in-var (make-var 0)] ...) ; Create blank dummy variables for each identifier.
		(build-substitution
		 state package substitution grounding
		 ((out-var (p-car . p-cdr)) ...) ; Unify each external destructured variable with its pattern in a new empty substitution.
		 (let ([in-var (mini-reify substitution in-var)] ...) ; Reify each fresh variable in the substitution to see if it is already bound by the pattern match with a ground term in the destructured external variable.
		   (values
		    (or (not (var? out-var)) ...) ; If one out-var is ground/bound, consider this relation structurally recursive and keep expanding it in the goal interpreter.
		    (conj*
		      (== out-var (mini-reify substitution out-var)) ... ; Generate unifications of each external variable with its reified pattern, which has extracted all possible ground information from both the external variable and the pattern itself due to the double reification.
		      body ...)
		    (set-state-varid ; Set as many variable ids as needed for fresh variables that remain fresh and so must enter the larger search as unbound variables.
		     state (fold-left
			    (lambda (id v)
			      (if (and (var? v) (fx= 0 (var-id v))) 
				  (begin (set-var-id! v id) (fx1+ id)) id))
			    (state-varid state) (list in-var ...)))
		    package)))))))])))


