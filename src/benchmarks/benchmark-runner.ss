(library (benchmark-runner)
  (export bench benchmark-testing)
  (import (chezscheme))
  (define benchmark-testing (make-parameter #f))
  (define-syntax bench
    (syntax-rules ()
      [(_ name iterations benchmark)
       (if (benchmark-testing)
	   (begin benchmark (void))
	   (printf "~s\t~s~%" name
		   (list-ref
		    (sort time<?
			  (map (lambda (n)
				 (collect)
				 (let ([start (current-time)])
				   benchmark
				   (time-difference (current-time) start)))
			       (iota (if (odd? iterations) iterations
					 (fx+ iterations 1))))) (fxquotient iterations 2))))])))
