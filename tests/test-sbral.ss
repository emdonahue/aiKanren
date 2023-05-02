(tassert "sbral add 1" (sbral-cons 1 sbral-empty) (vector 'sbral 1 1 sbral-empty))
(tassert "sbral add 2" (sbral-cons 2 (sbral-cons 1 sbral-empty))
	 (vector 'sbral 2 2 (vector 'sbral 1 1 sbral-empty)))
(tassert "sbral add 3" (sbral-cons 3 (sbral-cons 2 (sbral-cons 1 sbral-empty)))
	 (vector 'sbral (vector 'sbral-tree 3 3 2 1) 3 sbral-empty))
(tassert "sbral add 4" (sbral-cons 4 (sbral-cons 3 (sbral-cons 2 (sbral-cons 1 sbral-empty))))
	 (vector 'sbral 4 4 (vector 'sbral (vector 'sbral-tree 3 3 2 1) 3 sbral-empty)))
(tassert "sbral add 5" (sbral-cons 5 (sbral-cons 4 (sbral-cons 3 (sbral-cons 2 (sbral-cons 1 sbral-empty)))))
	 (vector 'sbral 5 5 (vector 'sbral 4 4 (vector 'sbral (vector 'sbral-tree 3 3 2 1) 3 sbral-empty))))
(tassert "sbral add 6" (sbral-cons 6 (sbral-cons 5 (sbral-cons 4 (sbral-cons 3 (sbral-cons 2 (sbral-cons 1 sbral-empty))))))
	 (vector 'sbral (vector 'sbral-tree 6 3 5 4) 6 (vector 'sbral (vector 'sbral-tree 3 3 2 1) 3 sbral-empty)))
(tassert "sbral add 7"
	 (sbral-cons 7 (sbral-cons 6 (sbral-cons 5 (sbral-cons 4 (sbral-cons 3 (sbral-cons 2 (sbral-cons 1 sbral-empty)))))))
	 (vector 'sbral (vector 'sbral-tree 7 7 (vector 'sbral-tree 6 3 5 4) (vector 'sbral-tree 3 3 2 1)) 7 sbral-empty))

(do ([i 1 (+ i 1)]) ((= i 4)) ; Build a sbral of this length, 
  (let ([s (fold-left (lambda (r e) (sbral-cons e r)) sbral-empty (iota i))])
    (do ([j 1 (+ j 1)]) ((< i j)) ;and confirm it contains these values
     (tassert "sbral-ref" (sbral-ref s j) j))))

