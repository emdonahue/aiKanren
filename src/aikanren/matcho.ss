(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution) (ui))

  (define-syntax build-substitution
    (syntax-rules ()
      [(_) '()]
      [(_ (v p) b ...) (mini-unify (build-substitution b ...) v (build-pattern p))]))
  
  (define-syntax build-pattern
    (syntax-rules (quote)
      [(_ (quote q)) 'q]
      [(_ (h . t)) (cons (build-pattern h) (build-pattern t))]
      [(_ ()) '()]
      [(_ v) v]))

  (define-syntax (matcho x)
    (define (analyze-pattern pattern)
      (if (pair? pattern) (cons (analyze-pattern (car pattern))
				(analyze-pattern (cdr pattern)))
	  (syntax-case pattern ()
	    [() '()]
	    [v (identifier? #'v) #'v]
	    [(h . t) (cons #'h (analyze-pattern #'t))]
	    [a #'a])))


    (define pattern-vars
      ;; Extracts unique identifiers from arbitrary pattern.
      (case-lambda
	[(pattern) (pattern-vars (analyze-pattern pattern) '())]
	[(pattern vs)
	 (cond
	  [(identifier? pattern) (if (memp (lambda (e) (bound-identifier=? e pattern)) vs) vs (cons pattern vs))]
	  [(pair? pattern) (pattern-vars (car pattern) (pattern-vars (cdr pattern) vs))]
	  [else vs])]))
    
    (syntax-case x ()
      [(_ ([v (p-car . p-cdr)] ...) body ...)
       (with-syntax ([(in-var ...) (pattern-vars #'((p-car . p-cdr) ...))])
	 #`(lambda (state package)
	     (let ([in-var (make-var 0)] ...)
	       (let ([substitution (build-substitution (v (p-car . p-cdr)) ...)])
		 (if (failure? substitution) (values fail failure package)
		     (let* ([varid (state-varid state)]
			    [in-var (mini-reify substitution in-var)] ...
			    [varid (if (and (var? in-var) (fx= 0 (var-id in-var)))
				       (begin (set-var-id! in-var varid) (fx1+ varid)) varid)] ...)
;		       (printf "~s\t~s~%" substitution (list (== (build-pattern v) (mini-reify substitution (build-pattern v))) ...))
		       (values
			(fresh ()
			  (== (build-pattern v) (mini-reify substitution (build-pattern v))) ...
			  body ...)
			(set-state-varid state varid)
			package)))))))])))


