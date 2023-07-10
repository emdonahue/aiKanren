;; Utilities for working with multiple value returns
;;TODO create an assert macro that produces nothing when compiled at optimization level 3 and ditch the entire assertion trimming mechanism. need to also account for profiling though, so maybe disable them with a parameter as well
(library (utils)
  (export with-values values-car values->list values-ref
	  org-define org-lambda org-case-lambda org-trace org-cond org-exclusive-cond org-printf org-display org-max-depth
	  nyi)
  (import (chezscheme))

  ;; === VALUES ===
  (define-syntax with-values
    (syntax-rules ()
      [(_ vals proc) (call-with-values (lambda () vals) proc)]))

  (define-syntax values-car
    (syntax-rules ()
      [(_ vals) (with-values vals (lambda (first . rest) first))]))

  (define-syntax values->list
    (syntax-rules ()
      [(_ vals) (with-values vals list)]))

  (define-syntax values-ref
    (syntax-rules ()
      [(_ vals n) (list-ref (values->list vals) n)]))


  (define-syntax nyi
    (syntax-rules ()
      [(_) (nyi nyi)]
      [(_ message ...) (assertion-violation (string-append (string-append (symbol->string 'message) " ") ...) "Not Yet Implemented")]))
  
  ;; === ORG-TRACE ===
  ;; Operates like trace-* but prints Emacs org-mode file in which nested calls are collapsible headers

  ;; TODO look at https://github.com/cisco/ChezScheme/issues/128 for discussion of other tracing options
  
  (define trace-depth (make-parameter 1))
  (define org-max-depth (make-parameter 0))
  (define trace-on (make-parameter #f))
    
  (define-syntax org-trace
    (syntax-rules ()
      [(_ body ...)
       (parameterize ([trace-on #t])
	 body ...)]))

  (define (org-printf . args)
    (when (trace-on) (apply printf args)) (apply values (cdr args)))

  (define (org-print-header header)
    (org-printf "~a ~a~%" (make-string (trace-depth) #\*) header))

  (define (org-print-item name value)
    (org-printf " - ~a: " name)
    (parameterize ([pretty-initial-indent (+ 3 (string-length (if (string? name) name (symbol->string name))))]
		   [pretty-standard-indent 0])
      (when (trace-on) (pretty-print value)))
    (org-printf "~%"))

  (define-syntax org-display
    (syntax-rules ()
      [(_ expr)
       (let ([val expr])
	 (when (trace-on) (org-print-item 'expr val))
	 val)]))
  
  (define-syntax org-lambda
    (syntax-rules ()
      [(_ name (arg ...) body0 body ...)
       (lambda (arg ...)
	 (org-print-header `name)
	 (if (fx= (trace-depth) (org-max-depth)) (assertion-violation 'name "org-max-depth reached")
	  (parameterize ([trace-depth (fx1+ (trace-depth))])
	    (org-print-header "arguments")
	    (org-print-item 'arg arg) ...
	    (org-print-header "logging") ;TODO make logging print lazily only if you log something at that trace level
	    (let ([return (call-with-values (lambda () body0 body ...) list)])
	      (org-print-header "return")
	      (for-each (lambda (i r) (org-print-item (number->string i) r)) (enumerate return) return)
	      (parameterize ([trace-depth (fx1- (trace-depth))])
		(org-print-header "logging"))
	      (apply values return)))))]))

  (define-syntax org-case-lambda
    (syntax-rules ()
      [(_ name [(arg ...) body ...] ...)
       (case-lambda
	 [(arg ...) ((org-lambda name (arg ...) body ...) arg ...)] ...)]))
  
  (define-syntax org-cond
    (syntax-rules (else)
      [(_ (head body ...) ...)
       (org-cond cond (head body ...) ...)]
      [(_ name (head body ...) ...)
       (cond
	[head ((org-lambda name (branch) body ...) 'head)] ...)]))

  (define-syntax org-exclusive-cond (identifier-syntax org-cond))
  
  (define-syntax org-define
    (syntax-rules ()
      [(_ (var . idspec) body ...) (define var (org-lambda var idspec body ...))])))



