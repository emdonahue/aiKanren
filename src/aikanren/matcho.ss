;; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables ""
(library (matcho)
  (export matcho matcho-pair)
  (import (chezscheme) (datatypes) (mini-substitution) (ui) (state))
  
  (define-syntax build-substitution
    ;; Walks each out-variable in turn and unifies it with its pattern, failing the entire computation if any pattern unification fails before walking subsequent variables.
    (syntax-rules ()
      [(_ state package substitution grounding ((out-var pattern)) body ...)
       (let* ([out-var (if (null? grounding) (walk state out-var) (car grounding))]
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

  (define-syntax matcho-pair
    (syntax-rules ()
      [(_ ([out-var (p-car . p-cdr)]) body ...)
       (exclusive-cond
	[(var? out-var)
	 (make-matcho
	  (list out-var) ;TODO equip matcho with the patterns externally to fail constraints without invoking goal. 
	  '()
	  (lambda (state package grounding)
	    (let ([out-var (if (null? grounding) (walk state out-var) (car grounding))])
	      (if (not (or (var? out-var) (pair? out-var)))
		  (values #t fail failure package)
		  (values
		   (not (var? out-var)) ; If one out-var is ground/bound, consider this relation structurally recursive and keep expanding it in the goal interpreter.
		   (let ([p-car (if (var? out-var) (make-var (state-varid state)) (car out-var))]
			 [p-cdr (if (var? out-var) (make-var (fx1+ (state-varid state))) (cdr out-var))])
		     (fresh () succeed body ...))
		   (if (var? out-var) (set-state-varid state (fx+ 2 (state-varid state))) state)
		   package)))))] ;(matcho ([out-var (p-car . p-cdr)]) body ...)
	[(pair? out-var)
	 (let ([p-car (car out-var)]
	       [p-cdr (cdr out-var)])
	   (fresh () succeed body ...))]
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
		    (fresh ()
		      (== out-var (mini-reify substitution out-var)) ... ; Generate unifications of each external variable with its reified pattern, which has extracted all possible ground information from both the external variable and the pattern itself due to the double reification.
		      body ...)
		    (set-state-varid ; Set as many variable ids as needed for fresh variables that remain fresh and so must enter the larger search as unbound variables.
		     state (fold-left
			    (lambda (id v)
			      (if (and (var? v) (fx= 0 (var-id v))) 
				  (begin (set-var-id! v id) (fx1+ id)) id))
			    (state-varid state) (list in-var ...)))
		    package)))))))])))


