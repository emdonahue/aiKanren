(import (benchmark-runner))

(bench "mplus" 100
       (run* (x)
	 (let recur ([n 12])
	   (if (zero? n) (== 1 1)
	       (conde [(recur (- n 1))]
		      [(recur (- n 1))])))))
