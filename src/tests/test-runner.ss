;;TODO make tassert capture file and line number
(library (test-runner)
  (export tassert tmessage)
  (import (chezscheme))

  (define failed (make-parameter 0))
  (define total (make-parameter 0))

  (define (tmessage)
    (if (= 0 (failed)) (printf "All Tests Pass (~s)~%" (total))
	(printf "Tests Failed: ~s/~s~%" (failed) (total))))
  
  (define-syntax tassert
    (syntax-rules ()
      [(_ title received! expected!)
       (with-exception-handler
	(lambda (e)
	  (printf "Exception in ~s~%" title)
	  (failed (fx1+ (failed)))
	  (raise e))
	(lambda ()
	  (total (fx1+ (total)))
	  (let* ([expected expected!]
		 [received-values (call-with-values (lambda () received!) list)]
		 [received (if (fx= 1 (length received-values)) (car received-values) received-values)])
	    (when (and (not (equal? expected received)) (or (not (procedure? expected)) (not (expected received))))
	      (failed (fx1+ (failed)))
	      (parameterize ([pretty-initial-indent 10]
			     [pretty-standard-indent 0])
		(printf "Failed: ~s~%Expected: " title)
		(pretty-print (if (procedure? expected) 'expected! expected))
		(printf "Received: ")
		(pretty-print received)
		(printf "~%"))))))])))
