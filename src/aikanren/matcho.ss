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

    (define extract-vars
      (case-lambda
	[(pattern) (extract-vars pattern '())]
	[(pattern vs)
	 (if (pair? pattern) (extract-vars (car pattern) (extract-vars (cdr pattern) vs))
	     (syntax-case pattern ()
	       [v (identifier? #'v)
		  (if (memp (lambda (e) (bound-identifier=? e #'v)) vs) vs (cons #'v vs))]
	       [(h . t) (extract-vars #'h (extract-vars #'t vs))]
	       [a vs]))]))
    
    (syntax-case x ()
      [(_ ([v (p-car . p-cdr)] ...) body ...)
       (with-syntax ([(in-var ...)
		      (extract-vars #'(p-car ... p-cdr ...))])
	 #`(lambda (state package)
	     (let ([in-var (make-var 0)] ...)
	       (let ([substitution (build-substitution (v (p-car . p-cdr)) ...)])
		 (if (failure? substitution) (values fail failure package)
		     (let* ([varid (state-varid state)]
			    [in-var (mini-reify substitution in-var)] ...
			    [varid (if (and (var? in-var) (fx= 0 (var-id in-var)))
				       (begin (set-var-id! in-var varid) (fx1+ varid)) varid)] ...)
		       (values
			(fresh ()
			  (== v (mini-reify substitution v)) ...
			  body ...)
			(set-state-varid state varid)
			package)))))))])))


