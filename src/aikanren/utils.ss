;; Utilities for working with multiple value returns
(library (utils)
  (export with-values first-value list-values values-ref org-define org-lambda org-case-lambda)
  (import (chezscheme))

  (define-syntax with-values
    (syntax-rules ()
      [(_ vals proc) (call-with-values (lambda () vals) proc)]))

  (define-syntax first-value
    (syntax-rules ()
      [(_ vals) (with-values vals (lambda (first . rest) first))]))

  (define-syntax list-values
    (syntax-rules ()
      [(_ vals) (with-values vals list)]))

  (define-syntax values-ref
    (syntax-rules ()
      [(_ vals n) (list-ref (list-values vals) n)]))

  (define trace-depth (make-parameter 1))

  ;; === ORG-TRACE ===
  ;; Operates like trace-* but prints Emacs org-mode file in which nested calls are collapsible headers
  
  (define-syntax org-lambda
    (syntax-rules ()
      [(_ name (arg ...) body0 body ...)
       (lambda (arg ...)
	 (printf "~a ~s~%" (make-string (trace-depth) #\*) 'name)
	 (parameterize ([trace-depth (fx1+ (trace-depth))])
	   (printf "~a ~s~%" (make-string (trace-depth) #\*) "arguments")
	   (begin (printf " - ~a: " 'arg)
		  (parameterize ([pretty-initial-indent 3]
				 [pretty-standard-indent 0])
		    (pretty-print arg))
		  (printf "~%")) ...
		  (printf "~a ~s~%" (make-string (trace-depth) #\*) "logs")
	   (let ([return (call-with-values (lambda () body0 body ...) list)])
	     (printf "~a ~s~%" (make-string (trace-depth) #\*) "return")
	     (for-each (lambda (r) (printf " - ")
			       (parameterize ([pretty-initial-indent 3]
					      [pretty-standard-indent 0])
				 (pretty-print r))
			       (printf "~%")) return)
	     (apply values return))))]))

  (define-syntax org-case-lambda
    (syntax-rules ()
      [(_ name [(arg ...) body ...] ...)
       (case-lambda
	 [(arg ...) ((org-lambda name (arg ...) body ...) arg ...)] ...)]))
  
  (define-syntax org-define
    (syntax-rules ()
      [(_ (var . idspec) body ...) (define var (org-lambda var idspec body ...))]))
  )



