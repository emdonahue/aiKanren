(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes)) 


  
  (define-syntax matcho
    (lambda (x)

      (define (analyze-pattern pattern)
	(syntax-case pattern ()
	  [() '()]
	  [v (identifier? #'v) #'v]
	  [(h . t) (cons #'h (analyze-pattern #'t))]
	  [a #'a]))


      (define pattern-vars
	(case-lambda
	  [(pattern) (pattern-vars (analyze-pattern pattern) '())]
	  [(pattern vs)
	   (cond
	    [(identifier? pattern) (if (memp (lambda (e) (bound-identifier=? e pattern)) vs) vs (cons pattern vs))]
	    [(pair? pattern) (pattern-vars (car pattern) (pattern-vars (cdr pattern) vs))]
	    [else vs])]))
      
      (define get-vars
	(lambda (vp)
	  (printf "input ~s~%" (syntax->list (cadar vp)))
	  (printf "pattern analysis ~s~%" (analyze-pattern (cadar vp)))
	  (printf "pattern vars ~s~%" (pattern-vars (cadar vp)))
	  (pattern-vars (cadar vp))))
      
      (syntax-case x ()
	[(m ([v pattern] ...) body ...)
	 (let ([vs (get-vars #'([v pattern] ...))])
	   #`(let ([#,(car vs) 3]) (body ...)))])))



  
  ) 
