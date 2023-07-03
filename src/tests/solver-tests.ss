(library (solver-tests) ; Tests the core mechanisms of the constraint solver
  (export run-solver-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (utils))
  
  (define (run-solver-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))
    (define x4 (make-var 4))

    ;; === CON/DISJUNCTION ===
    (tassert "conj fail first" (conj fail succeed) fail)
    (tassert "conj fail rest" (conj succeed fail) fail)
    (tassert "conj compress succeed" (conj succeed succeed) succeed)
    (tassert "conj single goals" (conj* (== 1 1)) (== 1 1))
    (tassert "conj keep normal goals" (conj* (== 1 1) succeed (== 2 2)) (conj* (== 1 1) (== 2 2)))

    (tassert "disj succeed first" (disj succeed fail) succeed)
    (tassert "disj succeed rest" (disj fail succeed) succeed)
    (tassert "disj compress fail" (disj fail fail) fail)
    (tassert "disj single goals" (disj* (== 1 1)) (== 1 1))
    (tassert "disj keep normal goals" (disj* (== 1 1) fail (== 1 1)) (disj (== 1 1) (== 1 1)))

    ;; === SOLVER ===
    (tassert "constraint ==" (run1 (x1) (constrain (== x1 1))) 1)
    (tassert "constraint =/=" (run1 (x1) (constrain (=/= x1 1))) (=/= x1 1))
    (tassert "constraint fail|succeed" (run1 (x1) (constrain (conde [(== x1 1) (== x1 2)] [(== 3 3)]))) x1)
    (tassert "constraint fail|==" (run1 (x1) (constrain (conde [(== x1 1) (== x1 2)] [(== x1 3)]))) 3)
    (tassert "constraint ==|== ==" (run1 (x1) (constrain (conde [(== x1 1)] [(== x1 2)])) (constrain (== x1 1))) 1)
    (tassert "constraint =/= ==|==" (run1 (x1) (constrain (=/= x1 1)) (constrain (conde [(== x1 1)] [(== x1 2)]))) 2)
    (tassert "constraint ==|== =/=" (run1 (x1) (constrain (conde [(== x1 1)] [(== x1 2)])) (constrain (=/= x1 1))) 2)
    (tassert "constraint &" (run1 (x1 x2) (== x1 1) (=/= x2 2)) (list 1 (=/= x2 2)))
    (tassert "constraint |" (run1 (x1) (constrain (conde ((== x1 1)) ((== x1 2))))) (disj* (== x1 1) (== x1 2)))
    (tassert "constraint == fail|==" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x1 2)) ((== x2 2))))) '(1 2))
    (tassert "constraint == succeed|==" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x1 1)) ((== x2 2))))) (list 1 x2))
    (tassert "constraint == ==|fail" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x2 2)) ((== x1 2))))) '(1 2))
    (tassert "constraint == ==|succeed" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x2 2)) ((== x1 1))))) (list 1 x2))
    (tassert "constraint == ==|succeed(out)" (run1 (x1 x2 x3) (constrain (== x1 1)) (constrain (== x3 3) (conde ((== x2 2)) ((== x1 1))))) (list 1 x2 3))
    (tassert "constraint == ==|==|=="
	     (run1 (x1 x2 x3) (constrain (== x3 1))
		   (constrain (conde ((== x1 x3)) ((== x2 x3)) ((== x1 x3)))))
	     (list (disj (== x1 1) (disj (== x2 1) (== x1 x3)))
		   (disj (== x1 1) (disj (== x2 1) (== x1 x3))) 1))
    (tassert "constraint ==|== ==" (run1 (x1) (constrain (conde ((== x1 1)) ((== x1 2)))) (constrain (== x1 1))) 1)
    (tassert "constraint =/=|=/= ==" (run1 (x1) (constrain (disj* (=/= x1 1) (=/= x1 2))) (constrain (== x1 1))) 1)
    (tassert "constraint =/=|=/= ==2" (run1 (x1 x2) ; =/= dont need to simplify, so just apply the == and move on
					    (constrain (disj* (=/= x1 1) (=/= x2 1)))
					    (constrain (== x2 1)))
	     (list (disj* (=/= x1 1) (=/= x2 1)) 1)) 
    (tassert "constraint simplification lvl 2" (run1 (x1 x2 x3 x4) (constrain (== x4 1)) (constrain (conde ((== x1 x4)) ((== x2 x4)) ((== x3 x4)))))
	     (list (disj (== x1 1) (disj (== x2 1) (== x3 x4))) (disj (== x1 1) (disj (== x2 1) (== x3 x4))) x3 1))
    (tassert "constraint =/=* fails &== failing all =/=" (run1 (x1 x2) (== x1 1) (== x2 2) (constrain (=/= (cons x1 x2) '(1 . 2)))) (void))
    (tassert "disj head disj preserves ctn" (run1 (x1 x2) (constrain (disj* (constraint (disj* (=/= x1 1) (=/= x1 1))) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
    (tassert "disj preserves ctn" (run1 (x1 x2) (constrain (disj* (=/= x1 1) (=/= x1 1) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
    
					;(pretty-print (run* (x1 x2) (disj* (conj* (== x1 1) (== x2 2)) (conj* (== x1 2) (== x2 1))) (=/= (cons x1 x2) '(1 . 2))))

					;(pretty-print (run1 (x1 x2) (constrain (disj (== x1 1) (== x1 2)) (== x2 3))))
    
    
					;(tassert "constraint =/=* collapses ==|== where 1 == fails all =/=" (run1 (x1 x2) (constrain (disj* (conj* (== x1 1) (== x2 2)) (conj* (== x1 2) (== x2 1)))) (constrain (=/= (cons x1 x2) '(1 . 2)))) '(2 1))
					;(pretty-print (run* (x1 x2) (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2))) (disj* (== x1 1) (== x2 1))))
					;(pretty-print (run* (x1 x2 x3) (constrain (disj* (== x1 1) (== x2 1)) (== x3 3)))) ; maybe if a state survives a conjunction we strap the full disjunction to it and send it on its way, thereby inverting the issue
					;(pretty-print (run* (x1) (constrain (disj* (== x1 1) (== x1 2)) (disj* (== x1 2) (== x1 3))))) succeeds
					; maybe we try joining the whole constraint inverted as a conj and seeing if we get a unique state back?, or a succeed goal. maybe we inspect the continuation first for disjs? maybe we put ourselves on the back of the continuation?  maybe we try the conjoined answer and if we get success we return the state, if we get partial success we push the rest into the state as a disjunction, if we get a failure we start testing our branches. maybe we do the normal tests and instead of returning we pack it into the state as a disj in lowest terms and re-run the future of the computation to see if anything tries to simplify against it. will need to prove this terminates, however
					;(exit)
					;(tassert "constraint ==|== collapses ==|(==&==)" (run1 (x1 x2) (constrain (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2)))) (constrain (disj* (== x1 1) (== x2 1)))) '(2 1))
					;(exit)

    ;;(tassert "constraint nested |" (run1 (x1 x2 x3) (constrain (disj* (conj* (== x1 1) (disj* (== x2 1) (== x3 1))) (== x1 2))) (== x3 3)) '(1 1 3)) TODO check that attr vars for diseq should be first 2 vs 1
    
    
    ;; === DISEQUALITY ===

    (tassert "disunify ground-self" (run* (q) (=/= 2 2)) '())
    (tassert "disunify ground-different" (run* () (=/= 1 2)) '(()))
    (tassert "disunify free-self" (run* (x1) (=/= x1 x1)) '())
    (tassert "disunify free-ground" (run1 (x1) (=/= x1 1)) (=/= x1 1))
    (tassert "disunify ground-free" (run1 (x1) (=/= 1 x1)) (=/= x1 1))
    (tassert "disunify free-free" (run1 (x1 x2) (=/= x1 x2)) (list (=/= x1 x2) x2))
    (tassert "disunify bound" (run* (x1) (== x1 1) (=/= x1 1)) '())
    (tassert "disunify check" (run* (x1) (=/= x1 1) (== x1 1)) '())
    (tassert "disunify free-ground x2" (run1 (x1) (=/= x1 2) (=/= x1 1)) (conj* (=/= x1 1) (=/= x1 2)))
    (tassert "disunify transfer to free then check" (run* (x1 x2) (=/= x1 2) (== x1 x2) (== x2 2)) '())
    (tassert "disunify lists" (car (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2)))) (disj* (=/= x1 1) (=/= x2 2)))
    (tassert "disunify fire lists" (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1)) (list 1 (=/= x2 2)))
    (tassert "disunify fire lists and fail" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1) (== x2 2)) '())
    (tassert "disunify simultaneous list diseq" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== (cons x1 x2) (cons 1 2))) '())
    (tassert "disunify simultaneous list diseq, fail on first" (run* (x1 x2) (=/= x1 1) (== (cons x1 x2) (cons 1 2))) '())
    (tassert "disunify simultaneous list diseq, fail on second" (run* (x1 x2) (=/= x2 2) (== (cons x1 x2) (cons 1 2))) '())
    (tassert "disunify transfer on free-free up varid" (run1 (x1 x2) (=/= x1 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
    (tassert "disunify transfer on free-free down varid" (run1 (x1 x2) (=/= x2 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))
    (tassert "disunify fire low varid" (run1 (x1 x2) (=/= x1 x2) (== x2 x1)) (void))
    (tassert "disunify conj" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x1 x2))
	     (list (conj* (=/= x2 1) (=/= x2 2)) (conj* (=/= x2 1) (=/= x2 2))))
    (tassert "disunify fire low varid" (run1 (x1 x2) (== x2 1) (=/= x1 1) (== x1 x2)) (void))
    (tassert "disunify fire high varid" (run1 (x1 x2) (== x1 1) (=/= x2 1) (== x1 x2)) (void))
    (tassert "disunify constraint cleared after fired"
	     (constraint-store-constraints (state-constraints (run1-states (x1) (=/= x1 1) (== x1 2)))) '())

    ;; === EQUALITY ===
    
    (tassert "==-c ground-self" (run1 (x1) (constrain (== 1 1))) x1)
    (tassert "==-c ground-different" (run1 (x1) (constrain (== 1 2))) (void))
    (tassert "==-c free-ground" (run1 (x1) (constrain (== x1 1))) 1)
    (tassert "==-c bound-ground-same" (run1 (x1) (== x1 1) (constrain (== x1 1))) 1)
    (tassert "==-c bound-ground-different" (run1 (x1) (== x1 2) (constrain (== x1 1))) (void))
    (tassert "==-c ground-bound-same" (run1 (x1) (constrain (== x1 1)) (== x1 1)) 1)
    (tassert "==-c ground-bound-different" (run1 (x1) (constrain (== x1 1)) (== x1 2)) (void))
    (tassert "==-c x ==-c conflict" (run1 (x1) (constrain (== x1 1)) (constrain (== x1 2))) (void))
    (tassert "==-c x ==-c no conflict" (run1 (x1) (constrain (== x1 1)) (constrain (== x1 1))) 1)
    (tassert "==-c & ==-c conflict" (run1 (x1) (constrain (conj* (== x1 2) (== x1 1)))) (void))
    (tassert "==-c & ==-c no conflict" (run1 (x1) (constrain (conj* (== x1 1) (== x1 1)))) 1)
    (tassert "==-c x =/=-c conflict" (run1 (x1) (=/= x1 1) (constrain (== x1 1))) (void))
    (tassert "==-c x =/=-c no conflict" (run1 (x1) (=/= x1 2) (constrain (== x1 1))) 1)
    (tassert "==-c | ==-c" (run1 (x1) (constrain (disj* (== x1 1) (== x1 2)))) (disj* (== x1 1) (== x1 2)))
    (tassert "==-c | ==-c attributes" (run1 (x1 x2) (constrain (disj* (== x1 1) (== x2 2)))) (list (disj* (== x1 1) (== x2 2)) (disj* (== x1 1) (== x2 2))))
    (tassert "==-c | ==-c simplifies bound"
	     (run1 (x1 x2) (== x1 1) (constrain (disj* (== x1 1) (== x2 2)))) (list 1 x2))
    (tassert "==-c | ==-c transfers bound"
	     (run1 (x1 x2) (== x1 3) (constrain (disj* (== x1 1) (== x2 2)))) (list 3 2))
    
))