(library (sbral-tests)
  (export run-sbral-tests)
  (import (chezscheme) (test-runner) (sbral))

  (define (run-sbral-tests)
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

    (tassert "sbral-ref 1" (sbral-ref (sbral-cons 1 sbral-empty) 0 -1) 1)
    (tassert "sbral-ref -11" (sbral-ref (sbral-cons 1 sbral-empty) -1 -2) -2)
    (tassert "sbral-ref 2.0" (sbral-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) 0 -1) 2)
    (tassert "sbral-ref 2.1" (sbral-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) 1 -1) 1)

    (tassert "sbral-set-ref 1" (sbral-ref (sbral-set-ref (sbral-cons 1 sbral-empty) 0 2 3) 0 -3) 2)
    (tassert "sbral-set-ref 2.0" (sbral-ref (sbral-set-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) 0 3 4) 0 -3) 3)
    (tassert "sbral-set-ref 2.1" (sbral-ref (sbral-set-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) 1 3 4) 1 -3) 3)
    (tassert "sbral-set-ref 2.-1" (sbral-ref (sbral-set-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) -1 3 4) 0 -3) 3)
    (tassert "sbral-set-ref 2.-2" (sbral-ref (sbral-set-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) -2 3 4) 0 -3) 3)
    (tassert "sbral-set-ref 2.-2 nil" (sbral-ref (sbral-set-ref (sbral-cons 2 (sbral-cons 1 sbral-empty)) -2 3 4) 1 -3) 4)

    (do ([i 1 (fx+ i 1)]) ((fx= i 50)) ; Build a sbral of this length, 
      (let ([s (fold-left (lambda (r e) (sbral-cons e r)) sbral-empty (iota i))])
	(do ([j 0 (fx+ j 1)]) ((fx= i j)) ;and confirm it contains these values
	  (tassert (string-append "sbral-ref " (number->string i) "@" (number->string j)) (sbral-ref s j -3) (fx- i j 1))
	  (tassert (string-append "sbral-set-ref " (number->string i) "@" (number->string j)) (sbral-ref (sbral-set-ref s j -1 -2) j -3) -1))))
))
