;; Utilities for working with multiple value returns
(library (utils)
  (export with-values first-value list-values values-ref org-define org-lambda org-case-lambda org-trace org-cond org-exclusive-cond org-printf)
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

  ;; TODO look at https://github.com/cisco/ChezScheme/issues/128 for discussion of other tracing options
  
  (define trace-depth (make-parameter 1))
  (define trace-on (make-parameter #f))
    
  (define-syntax org-trace
    (syntax-rules ()
      [(_ body ...)
       (parameterize ([trace-on #t])
	 body ...)]))

  (define (org-printf . args)
    (when (trace-on) (apply printf args)) (apply values (cdr args)))

  (define (org-printf-header header)
    (org-printf "~a ~s~%" (make-string (trace-depth) #\*) header))

  (define (org-printf-item name value)
    (org-printf " - ~a: " name)
    (parameterize ([pretty-initial-indent (+ 3 (string-length (if (string? name) name (symbol->string name))))]
		   [pretty-standard-indent 0])
      (when (trace-on) (pretty-print value)))
    (org-printf "~%"))
  
  (define-syntax org-lambda
    (syntax-rules ()
      [(_ name (arg ...) body0 body ...)
       (lambda (arg ...)
	 (org-printf-header 'name)
	 (parameterize ([trace-depth (fx1+ (trace-depth))])
	   (org-printf-header "arguments")
	   (org-printf-item 'arg arg) ...
		  (org-printf-header "logging")
	   (let ([return (call-with-values (lambda () body0 body ...) list)])
	     (org-printf-header "return")
	     (for-each (lambda (i r) (org-printf-item (number->string i) r)) (enumerate return) return)
	     (parameterize ([trace-depth (fx1- (trace-depth))])
	       (org-printf-header "logging"))
	     (apply values return))))]))

  (define-syntax org-case-lambda
    (syntax-rules ()
      [(_ name [(arg ...) body ...] ...)
       (case-lambda
	 [(arg ...) ((org-lambda name (arg ...) body ...) arg ...)] ...)]))
  
  (define-syntax org-cond
    (syntax-rules (else)
      [(_ (head body ...) ...)
       (cond
	[head (org-printf " - cond: ~a~%" 'head) body ...] ...)]
      [(_ name (head body ...) ...)
       (cond
	[head (org-printf " - cond (~a): ~a~%" 'name 'head) body ...] ...)]))

  (define-syntax org-exclusive-cond (identifier-syntax org-cond))
  
  (define-syntax org-define
    (syntax-rules ()
      [(_ (var . idspec) body ...) (define var (org-lambda var idspec body ...))])))



