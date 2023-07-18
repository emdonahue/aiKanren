;; Utilities for working with multiple value returns
(library (utils)
  (export with-values values-car values->list values-ref
	  cert
	  comment
	  org-define org-lambda org-case-lambda org-trace org-untrace org-cond org-exclusive-cond org-printf org-display org-max-depth org-print-header org-print-item org-depth org-tracing
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

  ;; === ASSERTIONS ===
  (define-syntax cert ;TODO have cert test conditions individually and print the failing condition
    (syntax-rules () ;;TODO update cert to produce nothing when compiled at optimization level 3 and ditch the entire assertion trimming mechanism. need to also account for profiling though, so maybe disable them with a parameter as well
      [(_ assertion ...) (when (zero? (optimize-level)) (assert assertion) ...)]))

  ;; === COMMENTING ===
  (define-syntax comment
    (syntax-rules ()
      [(_ comments ...) (void)]))
  
  ;; === ORG-TRACE ===
  ;; Operates like trace-* but prints Emacs org-mode file in which nested calls are collapsible headers

  ;; TODO look at https://github.com/cisco/ChezScheme/issues/128 for discussion of other tracing options
  
  (define org-depth (make-parameter 1))
  (define org-max-depth (make-parameter 0))
  (define org-tracing (make-parameter #f))
  (define is-logging (make-parameter #f))
    
  (define-syntax org-trace
    (syntax-rules ()
      [(_ body ...)
       (parameterize ([org-tracing #t])
	 body ...)]))

  (define-syntax org-untrace
    (syntax-rules ()
      [(_ body ...)
       (parameterize ([org-tracing #f])
	 body ...)]))

  (define (org-print-header header)
    (when (org-tracing)
      (is-logging #f)
      (printf "~a ~a~%" (make-string (org-depth) #\*) header)))

  (define org-print-item
    (case-lambda
      [(value)
       (when (org-tracing)
	 (pretty-print value))]
      [(name value)
       (when (org-tracing)
	 (printf " - ~a: " name)
	 (parameterize ([pretty-initial-indent (+ 4 (string-length (call-with-string-output-port (lambda (port) (write 'name port)))))]
			[pretty-standard-indent 0])
	   (pretty-print value))
	 (printf "~%"))]))

  (define (org-printf . args)
    (when (org-tracing)
      (when (not (is-logging)) (org-print-header "logging") (is-logging #t))
      (apply printf args)))
  
  (define-syntax org-display
    (syntax-rules ()
      [(_ expr ...)
       (begin
	(let ([val expr])
	  (when (org-tracing)
	    (when (not (is-logging)) (org-print-header "logging") (is-logging #t))
	    (org-print-item 'expr val))
	  val) ...)]))
  
  (define-syntax org-lambda
    (syntax-rules ()
      [(_ name (arg ...) body0 body ...)
       (lambda (arg ...)
	 (org-print-header `name)
	 (if (fx= (org-depth) (org-max-depth)) (assertion-violation 'name "org-max-depth reached")
	  (parameterize ([org-depth (fx1+ (org-depth))])
	    (org-print-header "arguments")
	    (org-print-item 'arg arg) ...
	    (let ([return (call-with-values (lambda () body0 body ...) list)])
	      (org-print-header "return")
	      (for-each (lambda (i r) (org-print-item (number->string i) r)) (enumerate return) return)
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



