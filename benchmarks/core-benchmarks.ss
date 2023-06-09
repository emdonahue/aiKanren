(import (benchmark-runner))

(bench "mplus" 1000
       (run* (x)
	 (let recur ([n 10])
	   (if (zero? n) (== 1 1)
	       (conde [(recur (- n 1))]
		      [(recur (- n 1))])))))
