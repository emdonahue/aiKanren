(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution) (ui))

  (define-syntax analyze-pattern2
    (syntax-rules ()
      [(_ (h . t)) (cons (analyze-pattern2 h) (analyze-pattern2 t))]
      [(_ ()) '()]
      [(_ v) v]))
  
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
    

    (define (build-substitution v-patterns)
      (if (null? v-patterns) #''()
	  #`(mini-unify #,(build-substitution (cdr v-patterns))
			#,(build-pattern (cadar v-patterns)) #,(caar v-patterns))))

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
#;
    (fold-left (lambda (sub evar-pattern)
    (mini-unify sub (car evar-pattern) (cdr evar-pattern)) '() ((v . (p-car . p-cdr)) ...)))

#;
(fold-left (lambda (sub evar-pattern)
    (mini-unify sub (car evar-pattern) (cdr evar-pattern))) '() (list (cons v (cons p-car p-cdr)) ...))

    
    (syntax-case x ()
      [(_ ([v (p-car . p-cdr)] ...) body ...)
       (with-syntax ([(in-var ...) (pattern-vars #'((p-car . p-cdr) ...))])
	 #`(lambda (state package)
	     (let ([in-var (make-var 0)] ...)
	       (printf "~s\t~s\t~s~%"
		       '([v (p-car . p-cdr)] ...)
		       (expand '(analyze-pattern2 ([v (p-car . p-cdr)] ...)))
		       (analyze-pattern2 ([v (p-car . p-cdr)] ...)))
	       (let ([substitution #,(build-substitution (analyze-pattern #'([v (p-car . p-cdr)] ...)))])
		 (if (failure? substitution) (values fail failure package)
		     #,(walk-vars #'(in-var ...) #'substitution
				  #`(values
				     (fresh () #,(build-extension (analyze-pattern #'([v (p-car . p-cdr)] ...)) #'substitution) body ...)
				     (mutate-vars #,(build-pattern #'(in-var ...))
						  state)
				     package)))))))])))
