(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes) (mini-substitution))

  #;
  (define-syntax matcho
    (syntax-rules ()
      [(_ ([v (pattern ...)]))]))


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

      #;
      (trace-define (build-unification v-patterns)

	#`#,(cadar v-patterns))

      (define (build-unification v-patterns)
	(printf "vpatterns: ~s~%" v-patterns)
	(if (null? v-patterns) #''()
	    #`(mini-unify #,(build-unification (cdr v-patterns)) #,(build-pattern (cadar v-patterns)) #,(caar v-patterns))))

      (trace-define (build-pattern pattern)
	(cond
	 [(null? pattern) #''()]
	 [(pair? pattern) #`(cons #,(build-pattern (car pattern)) #,(build-pattern (cdr pattern)))]
	 [else pattern]))
      #;
      (define (build-unification v-patterns sub body)
	(if (null? v-patterns) body
	    #`(let ([sub (mini-unify sub #,(cdar v-patterns) #,(caar v-patterns))])
		#,(build-unification (cdr v-patterns) #'sub body))))

      (define (walk-vars vs sub body)
	(if (null? vs) sub
	    #`(let ([#,(car vs) (mini-reify #,sub #,(car vs))])
		#,(walk-vars (cdr vs) sub body))))

      (syntax-case x ()
	[(_ ([v (p-car . p-cdr)] ...) body ...)
	 #`(lambda (state)
	     #,(build-vars
		(get-vars #'([v (p-car . p-cdr)] ...))
		#`(let ([substitution

			 #,(build-unification (analyze-pattern #'([v (p-car . p-cdr)] ...)))])
		    substitution
		    #;
		    #,(walk-vars (get-vars #'([v (pattern ...)] ...)) #'substitution #'(body ...)))))])))



)
