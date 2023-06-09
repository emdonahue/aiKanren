(import (benchmark-runner))

(bench "streams - answers" 100
       ;; Tests the speed at which we assemble our answer stream if there are no freshes to check for unnecessary suspension.
       (run* (x)
	 (let recur ([n 10])
	   (if (zero? n) (== 1 1)
	       (conde [(recur (- n 1))]
		      [(recur (- n 1))])))))

(bench "streams - mplus" 100
       ;; Pure interleaving speed
       (run* (x)
	 (let recur ([n 10])
	   (fresh (x)
	    (if (zero? n) (== 1 1)
		(conde [(recur (- n 1))]
		       [(recur (- n 1))]))))))

(bench "substitution - extend" 100
       ;; Extending the substitution without referencing the bindings
       (run* (x)
	 (let recur ([n 1000])
	   (fresh (y)
	    (if (zero? n) (== 1 1)
		(conde [(== y 1) (recur (- n 1))] ; Hide extension in a conj to avoid optimizations that skip substitution
		       [(== 1 2)]))))))
