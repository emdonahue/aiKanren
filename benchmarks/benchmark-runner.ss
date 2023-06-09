(library (benchmark-runner)
  (export bench)
  (import (chezscheme))
  
  (define-syntax bench
    (syntax-rules ()
      [(_ name iterations benchmark)
       (printf "~s\t~s~%" name
	       (list-ref
		(sort time<?
		      (map (lambda (n)
			     (collect)
			     (let ([start (current-time)])
			       benchmark
			       (time-difference (current-time) start)))
			   (iota (if (odd? iterations) iterations
				     (+ iterations 1))))) (+ (quotient iterations 2) 1)))])))
