(import (benchmark-runner))

(bench "answers" 100
       (run* (x)
	 (let recur ([n 10])
	   (if (zero? n) (== 1 1)
	       (conde [(recur (- n 1))]
		      [(recur (- n 1))])))))

(bench "mplus" 100
       (run* (x)
	 (let recur ([n 10])
	   (fresh (x)
	    (if (zero? n) (== 1 1)
		(conde [(recur (- n 1))]
		       [(recur (- n 1))]))))))
