(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution) (ui))

  #;
  (define-syntax matcho
    (syntax-rules ()
      [(_ ([v (pattern ...)]))]))

        (define (mutate-vars vs varid)
	(void))

  (define-syntax matcho
    (lambda (x)

      (define (analyze-pattern pattern)
	(if (pair? pattern) (cons (analyze-pattern (car pattern))
				  (analyze-pattern (cdr pattern)))
	    (syntax-case pattern ()
	      [() '()]
	      [v (identifier? #'v) #'v]
	      [(h . t) (cons #'h (analyze-pattern #'t))]
	      [a #'a])))


      (define pattern-vars
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

      (define get-vars
	(lambda (vp)
	  (printf "input ~s~%" (syntax->list (cadar vp)))
	  (printf "pattern analysis ~s~%" (analyze-pattern (cadar vp)))
	  (printf "pattern vars ~s~%" (pattern-vars (cadar vp)))
	  (pattern-vars (cadar vp))))

      (define (build-unification v-patterns)
	(printf "vpatterns: ~s~%" v-patterns)
	(if (null? v-patterns) #''()
	    #`(mini-unify #,(build-unification (cdr v-patterns)) #,(build-pattern (cadar v-patterns)) #,(caar v-patterns))))

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
      (define (mutate-vars vs varid body)
	#`(let ([varid #,(mutate-var vs varid)])
	    #,body))

      (define (mutate-var vs varid)
	(if (null? vs) varid
	    #`(if (and (var? #,(car vs)) (fx=? 0 (var-id #,(car vs))))
		  (begin (set-var-id! #,(car vs) #,varid) #,(mutate-var (cdr vs) #`(fx1+ #,varid)))
		  #,(car vs))))
      
      (syntax-case x ()
	[(_ ([v (p-car . p-cdr)] ...) body ...)
	 #`(lambda (state)
	     #,(build-vars
		(get-vars #'([v (p-car . p-cdr)] ...))
		#`(let ([substitution #,(build-unification (analyze-pattern #'([v (p-car . p-cdr)] ...)))])
		    #,(walk-vars (get-vars #'([v (p-car . p-cdr)] ...)) #'substitution
				 #`(begin
				     (mutate-vars #,(build-pattern (get-vars #'([v (p-car . p-cdr)] ...)))
						  #'(state-varid state))
				     (fresh () body ...))))))])))



)
