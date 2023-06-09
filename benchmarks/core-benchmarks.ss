(import (benchmark-runner))

(bench "substitution - extend" 100
       ;; Extending the substitution without referencing the bindings
       (run* (x)
	 (let recur ([n 400])
	   (fresh (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
	    (if (fx= 0 n) (== 1 1)
		(conde [(fresh (y)
			  (== x0 1) (== x1 1) (== x2 1)
			  (== x3 1) (== x4 1) (== x5 1)
			  (== x6 1) (== x7 1) (== x8 1)
			  (== x9 1) (recur (fx- n 1)))] ; Hide extension in a conj to avoid optimizations that skip substitution
		       [(fresh (y) (== 1 2))]))))))


(bench "streams - answers" 100
       ;; Tests the speed at which we assemble our answer stream if there are no freshes to check for unnecessary suspension.
       (run* (x)
	 (let recur ([n 10])
	   (if (fx= 0 n) (== 1 1)
	       (conde [(recur (fx- n 1))]
		      [(recur (fx- n 1))])))))

(bench "streams - mplus" 100
       ;; Pure interleaving speed
       (run* (x)
	 (let recur ([n 10])
	   (fresh (x)
	    (if (fx= 0 n) (== 1 1)
		(conde [(recur (fx- n 1))]
		       [(recur (fx- n 1))]))))))

(bench "substitution - extend" 100
       ;; Extending the substitution without referencing the bindings
       (run* (x)
	 (let recur ([n 400])
	   (fresh (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9)
	    (if (fx= 0 n) (== 1 1)
		(conde [(fresh (y)
			  (== x0 1) (== x1 1) (== x2 1)
			  (== x3 1) (== x4 1) (== x5 1)
			  (== x6 1) (== x7 1) (== x8 1)
			  (== x9 1) (recur (fx- n 1)))] ; Hide extension in a conj to avoid optimizations that skip substitution
		       [(fresh (y) (== 1 2))]))))))
