(library (matcho)
  (export matcho)
  (import (chezscheme) (datatypes)) 


  
  (define-syntax matcho
    (lambda (x)

      (define (analyze-pattern pattern)
	(syntax-case pattern ()
	  [() '()]
	  [v (identifier? #'v) #'v]
	  [(h . t) (cons #'h (analyze-pattern #'t))]))


      (define pattern-vars
	(case-lambda
	  [(pattern) (pattern-vars pattern '())]
	  [(pattern vs)
	   (cond
	    [(identifier? pattern) (cons pattern vs)]
	    [(pair? pattern) (pattern-vars (cdr pattern) (pattern-vars (car pattern) vs))]
	    [else vs])]))
      
      (define get-vars
	(lambda (vp)
	  (printf "input ~s~%" (syntax->list (cadar vp)))
	  (printf "pattern analysis ~s~%" (analyze-pattern (cadar vp)))
	  (printf "pattern vars ~s~%" (pattern-vars (analyze-pattern (cadar vp))))
	  '(b)))
      
      (syntax-case x ()
	[(m ([v pattern] ...) body ...)
	 (let ([vs (get-vars #'([v pattern] ...))])
	   `,#'(body ...))])))



  
  ) 
