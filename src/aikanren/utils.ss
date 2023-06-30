;; Utilities for working with multiple value returns
(library (utils)
  (export with-values first-value list-values values-ref org-define org-lambda org-case-lambda org-trace)
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


  ;; === ORG-TRACE ===
  ;; Operates like trace-* but prints Emacs org-mode file in which nested calls are collapsible headers
  
  (define trace-depth (make-parameter 1))
  (define trace-on (make-parameter #f))
    
  (define-syntax org-trace
    (syntax-rules ()
      [(_ body ...)
       (parameterize ([trace-on #t])
	 body ...
	 (when (fx= 1 (trace-depth)) (printf "* top level messages~%")))]))

  (define (org-print . args)
    (when (trace-on) (apply printf args)))
  
  (define-syntax org-lambda
    (syntax-rules ()
      [(_ name (arg ...) body0 body ...)
       (lambda (arg ...)
	 (org-print "~a ~s~%" (make-string (trace-depth) #\*) 'name)
	 (parameterize ([trace-depth (fx1+ (trace-depth))])
	   (org-print "~a ~s~%" (make-string (trace-depth) #\*) "arguments")
	   (begin (org-print " - ~a: " 'arg)
		  (parameterize ([pretty-initial-indent 3]
				 [pretty-standard-indent 0])
		    (when (trace-on) (pretty-print arg)))
		  (org-print "~%")) ...
		  (org-print "~a ~s~%" (make-string (fx1+ (trace-depth)) #\*) "logs")
	   (let ([return (call-with-values (lambda () body0 body ...) list)])
	     (org-print "~a ~s~%" (make-string (trace-depth) #\*) "return")
	     (for-each (lambda (r) (org-print " - ")
			       (parameterize ([pretty-initial-indent 3]
					      [pretty-standard-indent 0])
				 (when (trace-on) (pretty-print r)))
			       (org-print "~%")) return)	     
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



