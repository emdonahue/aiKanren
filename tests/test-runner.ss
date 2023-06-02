;;TODO make tassert capture file and line number
(library (test-runner)
  (export tassert)
  (import (chezscheme))
  
  (define-syntax tassert
    (syntax-rules ()
      [(_ title received expected)
       (with-exception-handler
	(lambda (e) (printf "Exception in ~s~%" title)
		(raise e))
	(lambda ()
	 (when (not (equal? expected received))
	   (printf "Failed: ~s~%    Expected: ~s~%    Received: ~s~%"
		   title expected received))))])))
