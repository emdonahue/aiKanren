(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner) (datatypes) (constraints) (state) (streams) (values))

  (define (ones v)
      (constrain
       (fresh (a d)
	 (== v (cons a d))
	 (disj* (== a 1) (ones d)))))
  
  (define (run-constraints-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    
    (tassert "disunify ground-self" (run* (q) (=/= 2 2)) '())
    (tassert "disunify ground-different" (run* () (=/= 1 2)) '(()))
    (tassert "disunify free-self" (run* (x1) (=/= x1 x1)) '())
    (tassert "disunify free-ground" (run1 (x1) (=/= x1 1)) (=/= x1 1))
    (tassert "disunify ground-free" (run1 (x1) (=/= 1 x1)) (=/= x1 1))
    (tassert "disunify free-free" (run1 (x1 x2) (=/= x1 x2))
	     (list (=/= x1 x2) (=/= x1 x2)))
    (tassert "disunify bound" (run* (x1) (== x1 1) (=/= x1 1)) '())
    (tassert "disunify check" (run* (x1) (=/= x1 1) (== x1 1)) '())
    (tassert "disunify free-ground x2" (run1 (x1) (=/= x1 2) (=/= x1 1))
	     (conj* (=/= x1 1) (=/= x1 2)))
    (tassert "disunify transfer to free then check" (run* (x1 x2) (=/= x1 2) (== x1 x2) (== x2 2)) '())
    (tassert "disunify lists" (car (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2))))
	     (disj* (=/= x1 1) (=/= x2 2)))    
    (tassert "disunify fire lists" (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1))
	     (list 1 (=/= x2 2)))
    (tassert "disunify fire lists and fail" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1) (== x2 2))
	     '())
    (tassert "disunify simultaneous list diseq" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== (cons x1 x2) (cons 1 2)))
	     '())
    (tassert "disunify simultaneous list diseq, fail on first" (run* (x1 x2) (=/= x1 1) (== (cons x1 x2) (cons 1 2)))
	     '())
    (tassert "disunify simultaneous list diseq, fail on second" (run* (x1 x2) (=/= x2 2) (== (cons x1 x2) (cons 1 2)))
	     '())

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
    (tassert "==-c | ==-c attributes" (run1 (x1 x2) (constrain (disj* (== x1 1) (== x2 2)))) (list (disj* (== x1 1) (== x2 2)) x2))
    (tassert "==-c | ==-c simplifies bound"
	     (run1 (x1 x2) (== x1 1) (constrain (disj* (== x1 1) (== x2 2)))) (list 1 x2))
    (tassert "==-c | ==-c transfers bound"
	     (run1 (x1 x2) (== x1 3) (constrain (disj* (== x1 1) (== x2 2)))) (list 3 2))

    (tassert "booleano free t" (run1 (x1) (booleano x1)) (constraint-goal (booleano x1)))
    (tassert "booleano bound t" (run1 (x1) (== x1 #t) (booleano x1)) #t)
    (tassert "booleano bound f" (run1 (x1) (== x1 #f) (booleano x1)) #f)
    (tassert "booleano bound undecidable fail" (run1 (x1) (== x1 'undecidable) (booleano x1)) (void))
    (tassert "booleano fired t" (run1 (x1) (booleano x1) (== x1 #t)) #t)
    (tassert "booleano fired f" (run1 (x1) (booleano x1) (== x1 #f)) #f)
    (tassert "booleano fired undecidable fail" (run1 (x1) (booleano x1) (== x1 'undecidable)) (void))

    (tassert "conj fail first" (normalized-conj* fail succeed) fail)
    (tassert "conj fail rest" (normalized-conj* succeed fail) fail)
    (tassert "conj compress succeed" (normalized-conj* succeed succeed) succeed)
    (tassert "conj single goals" (normalized-conj* (== 1 1)) (== 1 1))
    (tassert "conj keep normal goals" (normalized-conj* (== 1 1) succeed (== 1 1)) (conj* (== 1 1) (== 1 1)))
    (tassert "conj append conjs" (normalized-conj* (conj* (== 1 1) (== 2 2)) (conj* (== 3 3) (== 4 4))) (conj* (== 1 1) (== 2 2) (== 3 3) (== 4 4)))

    (tassert "disj succeed first" (normalized-disj* succeed fail) succeed)
    (tassert "disj succeed rest" (normalized-disj* fail succeed) succeed)
    (tassert "disj compress fail" (normalized-disj* fail fail) fail)
    (tassert "disj single goals" (normalized-disj* (== 1 1)) (== 1 1))
    (tassert "disj keep normal goals" (normalized-disj* (== 1 1) fail (== 1 1)) (disj* (== 1 1) (== 1 1)))
    (tassert "disj append disjs" (normalized-disj* (disj* (== 1 1) (== 2 2)) (disj* (== 3 3) (== 4 4))) (disj* (== 1 1) (== 2 2) (== 3 3) (== 4 4)))

    (tassert "cnf primitive" (conjunctive-normal-form (== 1 1)) (== 1 1))
    (tassert "cnf simple conj" (conjunctive-normal-form (conj* (== 1 1) (== 2 2))) (conj* (== 1 1) (== 2 2)))
    (tassert "cnf nested conj"
	     (conjunctive-normal-form
	      (conj* (conj* (== 1 1) (== 2 2)) (conj* (== 3 3) (== 4 4)))) (conj* (== 1 1) (== 2 2) (== 3 3) (== 4 4)))
    (tassert "cnf distribute single"
	     (conjunctive-normal-form
	      (disj* (== 1 1) (conj* (== 2 2) (== 3 3)))) (conj* (disj*  (== 1 1) (== 2 2)) (disj*  (== 1 1) (== 3 3))))
    (tassert "cnf distribute pairs"
	     (conjunctive-normal-form
	      (disj* (conj* (== 1 1) (== 2 2)) (conj* (== 3 3) (== 4 4)))) (conj* (disj*  (== 1 1) (== 3 3)) (disj*  (== 1 1) (== 4 4)) (disj*  (== 2 2) (== 3 3)) (disj*  (== 2 2) (== 4 4))))

    (tassert "presento ground succeed" (run1 () (presento 1 1)) '())
    (tassert "presento ground fail" (run1 () (presento 2 1)) (void))
    (tassert "presento bound ground term succeed" (run1 (x1) (== x1 1) (presento x1 1)) 1)
    
    (tassert "presento ground car succeed" (run1 () (presento (cons 1 2) 1)) '())
    (tassert "presento ground cdr succeed" (run1 () (presento (cons 2 1) 1)) '())
    (tassert "presento ground car succeed" (run1 () (presento (cons 2 2) 1)) (void))
    (tassert "presento ground cdr succeed" (run1 () (presento (cons 2 2) 1)) (void))
    (tassert "presento ground car succeed" (run1 () (presento (cons 1 2) 1)) '())
;;    (tassert "presento bound fail" (run1 (x1) (== x1 1) (presento x1 1)) 1)


					;    (display (run-constraint ))
    #;
    (display "START\n\n\n")
    #;
    (tassert "fresh-c increases varid" (state-varid (run-constraint empty-state (fresh (x1) (=/= x1 1)))) 2)
    #;
    (tassert "conj-c increases varid"
	     (state-varid (run-constraint empty-state
					  (conj* (fresh (x1) (=/= x1 1)) (fresh (x1) (=/= x1 1))))) 3)

    
    ;(tassert "ones list constraint" (run1 (x1) (ones (list 2 1))) '())
    ;;(tassert "presento fire ground term fail" (run1 (x1) (presento x1 1) (== x1 2)) (void))


    ;;(display (list-values (run-stream-constraint empty-state (conj* (== x1 1) (=/= x2 2)))))
    ;;(display (list-values (run-stream-constraint empty-state (disj* (== x1 1) (== x1 2)))))

    (display (run-stream-constraint (conj* (== x2 2) (== x1 1)) empty-state))
    
    ))
