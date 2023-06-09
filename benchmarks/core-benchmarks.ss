(import (benchmark-runner))

(bench "answers" 100
       ;; Tests the speed at which we assemble our answer stream if there are no freshes.
       (run* (x)
	 (let recur ([n 10])
	   (if (zero? n) (== 1 1)
	       (conde [(recur (- n 1))]
		      [(recur (- n 1))])))))

(bench "mplus" 100
       ;; Pure interleaving speed
       (run* (x)
	 (let recur ([n 10])
	   (fresh (x)
	    (if (zero? n) (== 1 1)
		(conde [(recur (- n 1))]
		       [(recur (- n 1))]))))))
