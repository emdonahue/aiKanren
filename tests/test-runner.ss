;;TODO make tassert capture file and line number
(library (test-runner)
  (export tassert)
  (import (chezscheme))
  
  (define-syntax tassert
    (syntax-rules ()
      [(_ title received! expected!)
       (with-exception-handler
	(lambda (e) (printf "Exception in ~s~%" title)
		(raise e))
	(lambda ()
	  (let ([expected expected!]
		[received received!])
	      (when (not (equal? expected received))
	     (parameterize ([pretty-initial-indent 10]
			    [pretty-standard-indent 0])
	       (printf "Failed: ~s~%Expected: " title)
	       (pretty-print expected)
	       (printf "Received: ")
	       (pretty-print received))))))])))
