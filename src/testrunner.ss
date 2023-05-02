(library (testrunner)
  (export tassert)
  (import (chezscheme))
  
  (define-syntax tassert
    (syntax-rules ()
      ((_ %title %received %expected)
       (begin
	 (let* ((title %title)
		(expected %expected)
		(received %received))
           (when (not (equal? expected received))
             (printf "Failed: ~s~%    Expected: ~s~%    Received: ~s~%"
                     title expected received))))))))
