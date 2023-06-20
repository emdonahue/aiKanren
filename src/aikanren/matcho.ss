(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution) (ui))

  (define (mutate-vars vs state)
    (let increment ([vs vs]
		    [varid (state-varid state)])
      (if (null? vs) (set-state-varid state varid)
	  (if (and (var? (car vs)) (zero? (var-id (car vs))))
	      (begin
		(set-var-id! (car vs) varid)
		(increment (cdr vs) (fx1+ varid)))
	      (increment (cdr vs) varid)))))

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

    (define (build-vars vs body)
      (if (null? vs) body
	  #`(let ([#,(car vs) (make-var 0)]) #,(build-vars (cdr vs) body))))

    (define (get-vars vp)
      (pattern-vars (cadar vp)))

    (define (build-unification v-patterns)
      (if (null? v-patterns) #''()
	  #`(mini-unify #,(build-unification (cdr v-patterns)) #,(build-pattern (cadar v-patterns)) #,(caar v-patterns))))

    (define (build-extension v-patterns substitution)
      (if (null? v-patterns) #'succeed
	  #`(make-conj (== #,(caar v-patterns) (mini-reify #,substitution #,(caar v-patterns)))
		       #,(build-extension (cdr v-patterns) substitution))))

    (define (build-pattern pattern)
      (cond
       [(null? pattern) #''()]
       [(pair? pattern) #`(cons #,(build-pattern (car pattern)) #,(build-pattern (cdr pattern)))]
       [else pattern]))

    (define (walk-vars vs sub body)
      (if (null? vs) body
	  #`(let ([#,(car vs) (mini-reify #,sub #,(car vs))])
	      #,(walk-vars (cdr vs) sub body))))
    
    (syntax-case x ()
      [(_ ([v (p-car . p-cdr)] ...) body ...)
       (let ([in-vars (pattern-vars #'((p-car . p-cdr) ...))])
	 #`(lambda (state package)
	     #,(build-vars
		in-vars
		#`(let ([substitution #,(build-unification (analyze-pattern #'([v (p-car . p-cdr)] ...)))])
		    (if (failure? substitution) (values fail failure package)
			#,(walk-vars in-vars #'substitution
				     #`(values
					(fresh () #,(build-extension (analyze-pattern #'([v (p-car . p-cdr)] ...)) #'substitution) body ...)
					(mutate-vars #,(build-pattern in-vars)
						     state)
					package)))))))])))
