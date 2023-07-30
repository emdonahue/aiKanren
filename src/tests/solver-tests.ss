(library (solver-tests) ; Tests the core mechanisms of the constraint solver
  (export run-solver-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (utils) (state) (solver))
  
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

    ;; === SUBSTITUTION ===
    (tassert "substitution constraint-ground fail" (run1 (x1) (=/= x1 1) (== x1 1)) (void))
    (tassert "substitution constraint-ground succeed" (run1 (x1) (=/= x1 1) (== x1 2)) 2)
    (tassert "substitution ground-constraint fail" (run1 (x1) (=/= x1 1) (== 1 x1)) (void))
    (tassert "substitution ground-constraint succeed" (run1 (x1) (=/= x1 1) (== 2 x1)) 2)
    (tassert "substitution constraint-bound fail" (run1 (x1) (== x1 1) (=/= x1 1)) (void))
    (tassert "substitution constraint-bound succeed" (run1 (x1) (== x1 2) (=/= x1 1)) 2)
    (tassert "substitution bound-constraint fail" (run1 (x1) (== 1 x1) (=/= x1 1)) (void))
    (tassert "substitution bound-constraint succeed" (run1 (x1) (== 2 x1) (=/= x1 1)) 2)
    (tassert "substitution constraint-free" (run1 (x1 x2) (=/= x1 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
    (tassert "substitution constraint-free high var" (run1 (x1 x2) (=/= x2 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
    (tassert "substitution free-constraint" (run1 (x1 x2) (=/= x1 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))
    (tassert "substitution free-constraint high var" (run1 (x1 x2) (=/= x2 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))
    
    (tassert "substitution constraint-constraint" (run1 (x1) (=/= x1 1) (=/= x1 2)) (conj (=/= x1 1) (=/= x1 2)))
    (tassert "substitution constraint-constraint-free" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x1 x2)) (list (conj (=/= x2 1) (=/= x2 2)) (conj (=/= x2 1) (=/= x2 2))))
    (tassert "substitution constraint-constraint-free2" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x2 x1)) (list (conj (=/= x2 1) (=/= x2 2)) (conj (=/= x2 1) (=/= x2 2))))
    (tassert "substitution constraint disunify free" (run1 (x1 x2) (=/= x1 1) (=/= x1 x2)) (list (conj (=/= x1 1) (=/= x1 x2)) x2))
    (tassert "substitution constraint disunify free2" (run1 (x1 x2) (=/= x2 1) (=/= x1 x2)) (list (=/= x1 x2) (=/= x2 1)))
    ;;TODO implement disunification solver
					;(org-trace    (tassert "substitution constraint disunify bound" (run1 (x1) (=/= x1 1) (=/= 1 x1)) (=/= x1 1)))

    (tassert "substitution pconstraint-ground fail" (run1 (x1) (symbolo x1) (== x1 1)) (void))
    (tassert "substitution ground-pconstraint fail" (run1 (x1) (== x1 1) (symbolo x1)) (void))
    (tassert "substitution pconstraint-ground succeed" (run1 (x1) (symbolo x1) (== x1 'symbol)) 'symbol)
    (tassert "substitution ground-pconstraint succeed" (run1 (x1) (== x1 'symbol) (symbolo x1)) 'symbol)
    (tassert "substitution pconstraint-constraint" (run1 (x1) (symbolo x1) (=/= x1 1)) (symbolo x1))
    (tassert "substitution pconstraint-constraint" (run1 (x1) (=/= x1 1) (symbolo x1)) (lambda (c) (and (conj? c) (equal? (conj-lhs c) (=/= x1 1)) (and (pconstraint? (conj-rhs c)) (equal? (pconstraint-vars (conj-rhs c)) (list x1))))))

    (tassert "eq? variables must not unify when constrained" (run1 (x1) (=/= x1 1) (== x1 x1)) (=/= x1 1))
    (tassert "eq? variables must not disunify when constrained" (run1 (x1) (=/= x1 1) (=/= x1 x1)) (void))

    ;; === ATTRIBUTED VARIABLES ===

    (tassert "disequalities attribute only to first var" (run1 (x1 x2) (=/= (cons x1 x2) '(1 . 2))) `(,(disj (=/= x1 1) (=/= x2 2)) ,x2))
    (tassert "disj of disequalities attribute only to first var" (run1 (x1 x2) (disj (=/= x1 1) (=/= x2 2))) `(,(disj (=/= x1 1) (=/= x2 2)) ,x2))


    ;; Single variable
    (tassert "attribute x1=1=>x1=/=x1=>fail" (run1 (x1) (disj (=/= x1 1) (== x1 2))) (disj (=/= x1 1) (== x1 2))) ; TODO can we simplify disjunctions of == and =/= of the same var? technically should be simplified to x1 =/= 1
    (tassert "attribute to negation if second and promote" (run1 (x1) (disj (== x1 1) (=/= x1 1))) (disj (=/= x1 1) (== x1 1)))
    (tassert "attribute ~1=>2,~2=>1" (run1 (x1) (disj (== x1 1) (== x1 2))) (disj (== x1 2) (== x1 1)))

    ;; Multi variable
    (tassert "attribute ~x1=>x2, ~x2=>x1" (run1 (x1 x2) (disj (== x1 1) (== x2 2)))
	     (list (disj (== x2 2) (== x1 1)) (disj (== x2 2) (== x1 1)))) 
    (tassert "attribute x1=>x2, ~x2=>x1" (run1 (x1 x2) (disj (== x1 1) (conj (== x1 1) (== x2 2)))) (list 1 x2))
    (tassert "attribute x1=>x2, x2=>x1" (run1 (x1 x2 x3) (disj (conj (== x1 1) (== x2 2)) (== x3 3)))
	     (list (disj (== x3 3) (conj (== x1 1) (== x2 2)))
		   (disj (== x3 3) (conj (== x1 1) (== x2 2)))
		   (disj (== x3 3) (conj (== x1 1) (== x2 2)))))
    (tassert "attribute == =/=" (run1 (x1 x2) (disj (== x1 1) (=/= x2 2)))
	     (list x1 (disj (=/= x2 2) (== x1 1))))
    (tassert "attribute =/= ==" (run1 (x1 x2) (disj (=/= x2 2) (== x1 1)))
	     (list x1 (disj (=/= x2 2) (== x1 1))))
    

    ;; Multi variable with negation
    (tassert "attribute x1:x1=1=>x2=2" (run1 (x1 x2) (disj (=/= x1 1) (== x2 2)))
	     (list (disj (=/= x1 1) (== x2 2)) x2))
    
    (tassert "attribute x1:x1=1=>x2=2, x3:x3~3=>x2=2, x2:x2~2=>x3=3" (run1 (x1 x2 x3) (disj (conj (=/= x1 1) (== x3 3)) (== x2 2)))
	     (list (disj (== x2 2) (conj (=/= x1 1) (== x3 3)))
		   (disj (== x2 2) (conj (=/= x1 1) (== x3 3)))
		   (disj (== x2 2) (conj (=/= x1 1) (== x3 3)))))

    ;; Multi variable with fresh
    (tassert "attribute x1:~x1=>x2=2" (run1 (x1 x2) (disj (matcho [(x1 (a . d))]) (== x2 2)))
	     (lambda (a) (and (disj? (car a)) (matcho? (disj-lhs (car a))) (equal? (disj-rhs (car a)) (== x2 2)) (equal? x2 (cadr a)))))
    
    ;; === SOLVER ===
    (tassert "constraint ==" (run1 (x1) (constrain (== x1 1))) 1)
    (tassert "constraint =/=" (run1 (x1) (constrain (=/= x1 1))) (=/= x1 1))
    (tassert "constraint fail|succeed" (run1 (x1) (constrain (conde [(== x1 1) (== x1 2)] [(== 3 3)]))) x1)
    (tassert "constraint fail|==" (run1 (x1) (constrain (conde [(== x1 1) (== x1 2)] [(== x1 3)]))) 3)
    (tassert "constraint ==|== ==" (run1 (x1) (constrain (conde [(== x1 1)] [(== x1 2)])) (constrain (== x1 1))) 1)
    (tassert "constraint =/= ==|==" (run1 (x1) (constrain (=/= x1 1)) (constrain (conde [(== x1 1)] [(== x1 2)]))) 2)
    (tassert "constraint ==|== =/=" (run1 (x1) (constrain (conde [(== x1 1)] [(== x1 2)])) (constrain (=/= x1 1))) 2)
    (tassert "constraint &" (run1 (x1 x2) (== x1 1) (=/= x2 2)) (list 1 (=/= x2 2)))
    (tassert "constraint |" (run1 (x1) (constrain (conde ((== x1 1)) ((== x1 2))))) (disj* (== x1 2) (== x1 1)))
    (tassert "constraint == fail|==" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x1 2)) ((== x2 2))))) '(1 2))
    (tassert "constraint == succeed|==" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x1 1)) ((== x2 2))))) (list 1 x2))
    (tassert "constraint == ==|fail" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x2 2)) ((== x1 2))))) '(1 2))
    (tassert "constraint == ==|succeed" (run1 (x1 x2) (constrain (== x1 1)) (constrain (conde ((== x2 2)) ((== x1 1))))) (list 1 x2))
    (tassert "constraint == ==|succeed(out)" (run1 (x1 x2 x3) (constrain (== x1 1)) (constrain (== x3 3) (conde ((== x2 2)) ((== x1 1))))) (list 1 x2 3))
    (tassert "constraint == ==|==|=="
	     (run1 (x1 x2 x3) (constrain (== x3 1))
		   (constrain (conde ((== x1 x3)) ((== x2 x3)) ((== x1 x3)))))
	     (list (disj (== x2 1) (disj (== x1 1) (== x1 x3)))
		   (disj (== x2 1) (disj (== x1 1) (== x1 x3))) 1))
    (tassert "constraint ==|== ==" (run1 (x1) (constrain (conde ((== x1 1)) ((== x1 2)))) (constrain (== x1 1))) 1)
    (tassert "constraint =/=|=/= ==" (run1 (x1) (constrain (disj* (=/= x1 1) (=/= x1 2))) (constrain (== x1 1))) 1)
    (tassert "constraint =/=|=/= ==2" (run1 (x1 x2) ; =/= dont need to simplify, so just apply the == and move on
					    (constrain (disj* (=/= x1 1) (=/= x2 1)))
					    (constrain (== x2 1)))
	     (list (disj* (=/= x1 1) (=/= x2 1)) 1)) 
    (tassert "constraint simplification lvl 2" (run1 (x1 x2 x3 x4) (constrain (== x4 1)) (constrain (conde ((== x1 x4)) ((== x2 x4)) ((== x3 x4)))))
	     (list (disj (== x2 1) (disj (== x1 1) (== x3 x4))) (disj (== x2 1) (disj (== x1 1) (== x3 x4))) x3 1))
    (tassert "constraint =/=* fails &== failing all =/=" (run1 (x1 x2) (== x1 1) (== x2 2) (constrain (=/= (cons x1 x2) '(1 . 2)))) (void))
    (tassert "disj head disj preserves ctn" (run1 (x1 x2) (constrain (disj* (constraint (disj* (=/= x1 1) (=/= x1 1))) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
    (tassert "disj preserves ctn" (run1 (x1 x2) (constrain (disj* (=/= x1 1) (=/= x1 1) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
    (tassert "disj only walks 1st disjunct if no ==" (run1 (x1 x2) (== x2 2) (constrain (conde [(=/= x1 1)] [(=/= x2 2)]))) (list (disj (=/= x1 1) (=/= x2 2)) 2))
    
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
    (tassert "disunify free-ground x2" (run1 (x1) (=/= x1 2) (=/= x1 1)) (conj* (=/= x1 2) (=/= x1 1)))
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
    (tassert "disunify fired constraints restored on failure" (run1 (x1) (disj (== x1 1) (== x1 1)) (=/= (list x1 x1) '(1 1))) (void))
    (tassert "disunify disjunction builds continuation" (run1 (x1) (disj (== x1 1) (== x1 2)) (=/= (list x1 x1) '(3 3)))
	     (conj (disj (=/= x1 3) (=/= (list x1) '(3))) (disj (== x1 1) (== x1 2))))
    (tassert "disunify disjunction runs ctn" (run1 (x1) (constrain (=/= (list x1 x1) '(1 1)) (== x1 1))) (void))
    (tassert "disunify disjunction runs ctn" (run1 (x1) (constrain (=/= (list x1 x1) '(1 1)) (== x1 1))) (void))

    (tassert "disunify simplify simple abort" (run1 (x1) (=/= x1 1) (=/= x1 1)) (=/= x1 1))
    (tassert "disunify simplify ignores conj" (run1 (x1) (=/= x1 1) (=/= x1 2) (=/= x1 3)) (conj (conj (=/= x1 1) (=/= x1 2)) (=/= x1 3)))
    (tassert "disunify simplify conj early succeed" (run1 (x1) (conj (=/= x1 1) (=/= x1 2)) (=/= x1 1)) (conj (=/= x1 1) (=/= x1 2)))
    (tassert "disunify simplify abort pconstraint" (run1 (x1) (symbolo x1) (=/= x1 1)) (symbolo x1))    
    (tassert "disunify simplify ignore pconstraint" (run1 (x1) (numbero x1) (=/= x1 1)) (conj (numbero x1) (=/= x1 1)))
    (tassert "disunify simplify abort negative pconstraint" (run1 (x1) (noto (numbero x1)) (=/= x1 1)) (noto (numbero x1)))
    (tassert "disunify simplify matcho succeed" (run1 (x1) (constrain (matcho ([x1 (a . d)]))) (=/= x1 1)) (lambda (c) (matcho? c)))
    (tassert "disunify simplify matcho" (run1 (x1) (constrain (matcho ([x1 (a . d)]))) (=/= x1 '(1 . 2))) (lambda (c) (and (conj? c) (equal? (conj-rhs c) (=/= x1 '(1 . 2))) (matcho? (conj-lhs c)))))
    (tassert "disunify simplify negative matcho" (run1 (x1) (constrain (noto (matcho ([x1 (a . d)])))) (=/= x1 1)) (lambda (c) (and (conj? c) (matcho? (noto-goal (conj-lhs c))) (equal? (conj-rhs c) (=/= x1 1)))))
    (tassert "disunify simplify disjunction fails first" (run1 (x1 x2) (disj (== x2 2) (== x1 1)) (=/= x1 1)) (list (=/= x1 1) 2))
    ;(tassert "disunify simplify disjunction succeeds" (run1 (x1) (disj (=/= x1 1) (symbolo x1)) (=/= x1 1)) (disj (=/= x1 1) (symbolo x1)))
        

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
    (tassert "==-c | ==-c" (run1 (x1) (constrain (disj* (== x1 1) (== x1 2)))) (disj* (== x1 2) (== x1 1)))
    (tassert "==-c | ==-c attributes" (run1 (x1 x2) (constrain (disj* (== x1 1) (== x2 2)))) (list (disj* (== x2 2) (== x1 1)) (disj* (== x2 2) (== x1 1))))
    (tassert "==-c | ==-c simplifies bound"
	     (run1 (x1 x2) (== x1 1) (constrain (disj* (== x1 1) (== x2 2)))) (list 1 x2))
    (tassert "==-c | ==-c transfers bound"
	     (run1 (x1 x2) (== x1 3) (constrain (disj* (== x1 1) (== x2 2)))) (list 3 2))

    ;; === DISJUNCTION ===

    (tassert "== factored out of disj" (run1 (x1) (disj (== x1 1) (== x1 1))) 1)
    (tassert "== factored out of nested disj" (run1 (x1 x2) (== x2 2) (disj (conj (== x2 2) (disj (== x1 1) (== x1 1))) (== x2 3))) '(1 2))
    (tassert "== factored out of nested disj tail" (run1 (x1 x2) (== x2 2) (disj (== x1 1) (conj (== x2 2) (disj (== x1 1) (== x1 1))))) '(1 2))
    (tassert "nested disj terminates disj solving" (run1 (x1 x2) (== x2 2) (disj (== x1 1) (conj (== x2 2) (disj (== x1 2) (== x1 1))))) (list (disj (== x1 1) (disj (== x1 1) (== x1 2))) 2))
;    (tassert "=/= & (=/=|numbero)" (run1 (x1) (disj (=/= x1 1) (numbero x1)) (=/= x1 1)) (=/= x1 1))
					;(tassert "=/= & (symbolo|numbero)" (run1 (x1) (disj (symbolo x1) (numbero x1)) (=/= x1 1)) (disj (symbolo x1) (conj (=/= x1 1) (numbero x1))))
    (tassert "=/= & (=/=|succeed)" (run1 (x1) (disj (numbero x1) (symbolo x1)) (=/= x1 1)) (conj (=/= x1 1) (disj (numbero x1) (symbolo x1))))
;    (tassert "=/= & (fail|succeed)" (run1 (x1 x2) (disj (conj (=/= x1 1) (== x2 2)) (== x1 1)) (=/= x1 1)) (list (=/= x1 1) 2))

    (tassert "== succeed" (simplify-=/=2 (== x1 1) x1 1) succeed)
    (tassert "== undecidable" (simplify-=/=2 (== x1 (cons x2 x3)) x1 (cons x3 x2)) succeed) 
    (tassert "symbolo fail" (simplify-=/=2 (symbolo x1) x1 1) fail)
    (tassert "not numbero fail" (simplify-=/=2 (noto (numbero x1)) x1 1) fail)
    (tassert "=/= fail" (simplify-=/=2 (=/= x1 1) x1 1) fail)
    (tassert "=/= succeed" (simplify-=/=2 (=/= x1 2) x1 1) succeed)
    (tassert "conj fail" (simplify-=/=2 (conj (== x1 1) (=/= x1 1)) x1 1) fail)
    ))
