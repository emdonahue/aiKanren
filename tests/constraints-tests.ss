(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (ui) (test-runner) (datatypes) (constraints) (state) (streams) (values) (sbral))

  (define (run-constraints-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))
    (define stale (lambda (s p) (assert #f))) ; Fresh that should never be expanded

    (define unify
      (lambda (s x y)
	(first-value (unify-check s x y))))

    (define ones
      (lambda (v)
	(constrain
	 (fresh (a d)
	   (== v (cons a d))
	   (disj* (== a 1) (ones d))))))

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
    (tassert "disunify transfer on free-free up varid" (run1 (x1 x2) (=/= x1 1) (== x1 x2))
	     (list (=/= x2 1) (=/= x2 1)))
    (tassert "disunify transfer on free-free down varid" (run1 (x1 x2) (=/= x2 1) (== x2 x1))
	     (list (=/= x2 1) (=/= x2 1)))
    (tassert "disunify fire low varid" (run1 (x1 x2) (=/= x1 x2) (== x2 x1))
	     (void))
    (tassert "disunify conj" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x1 x2))
	     (list (conj* (=/= x2 1) (=/= x2 2)) (conj* (=/= x2 1) (=/= x2 2))))
    (tassert "disunify fire low varid" (run1 (x1 x2) (== x2 1) (=/= x1 1) (== x1 x2))
	     (void))
    (tassert "disunify fire high varid" (run1 (x1 x2) (== x1 1) (=/= x2 1) (== x1 x2))
	     (void))
    (tassert "disunify constraint cleared after fired"
	     (constraint-store-constraints (state-constraints (run1-states (x1) (=/= x1 1) (== x1 2)))) '())

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
    (tassert "conj keep normal goals" (normalized-conj* (== 1 1) succeed (== 2 2)) (conj* (== 1 1) (== 2 2)))
    (tassert "conj remove duplicates" (normalized-conj* (== 1 1) succeed (== 1 1)) (conj* (== 1 1)))
    (tassert "conj append conjs" (normalized-conj* (conj* (== 1 1) (== 2 2)) (conj* (== 3 3) (== 4 4))) (conj* (== 1 1) (== 2 2) (== 3 3) (== 4 4)))
    (tassert "conj remove duplicate conjs" (normalized-conj* (conj* (== 1 1) (== 2 2)) (conj* (== 2 2) (== 3 3))) (conj* (== 1 1) (== 2 2) (== 3 3)))

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

    
    (let* ([c (presento x1 1)]
	   [s (run1 (x1) c)])
      ;; #(disj (#(== #(var 1) 1) #<procedure at constraints.ss:509>))
      (tassert "presento unbound term succeed" (run1 (x1) c (== x1 1)) 1)
      (tassert "presento unbound term fail" (run1 (x1) c (== x1 2)) (void))
      (tassert "presento unbound term"
	       s
	       (disj* (== x1 1) ; car is not 1
		      (cadr ; car is not recursive pair
		       (disj-disjuncts s)))))
    
    (let* ([c (presento (cons x1 2) 1)]
	   [s (run1 (x1) c )])
      ;; #(disj (#(== #(var 2) 1) #<procedure at constraints.ss:509> #(constraint #(disj (#(== #(var 3) 1) #<procedure at constraints.ss:509>)))))
      (tassert "presento unbound car succeed" (run1 (x1) c (== x1 1)) 1)
      (tassert "presento unbound car fail" (run1 (x1) c (== x1 2)) (void))
      (tassert "presento unbound car"
	       s (disj* (== x2 1) ; car is not 1
			(cadr (disj-disjuncts s)) ; car is not recursive pair
			(make-constraint ; cdr
			 (disj* (== x3 1) ; cdr is not 1
				(cadr (disj-disjuncts ; cdr is not recursive pair
				       (constraint-goal (list-ref (disj-disjuncts s) 2)))))))))

    (let* ([c (presento (cons 2 x1) 1)]
	   [s (run1 (x1)  c)])
      ;; #(disj (#(== #(var 3) 1) #<procedure at constraints.ss:509>))
      (tassert "presento unbound cdr succeed" (run1 (x1) c (== x1 1)) 1)
      (tassert "presento unbound cdr fail" (run1 (x1) c (== x1 2)) (void))
      (tassert "presento unbound cdr"
	       s (disj* (== x3 1) ; cdr is not 1
			(cadr ; car is not recursive pair
			 (disj-disjuncts s)))))

    ;;    (display "START\n\n")

    
    ;;(tassert "presento fuzz succeed" (run1 (x1) (presento (cons (list 2 3 4 5 x1 ) 6) 1) (== x1 1)) 1)
    ;;(tassert "presento fuzz succeed" (run1 (x1) (presento (cons (list 2 3 4 5 x1) 6) 1) (== x1 1)) 1)
    ;;(tassert "presento fuzz succeed" (run1 (x1) (presento (cons (cons (cons (list 2 3 x1) 7) 2) 6) 1) (== x1 1)) 1)
    #;
    (tassert "presento fuzz succeed" (run1 (x1) (presento (list 2 (list 3 (cons 4 (cons 5 (cons 6 x1))))) 1) (== x1 1)) 1)
    #;
    (let ([s (run1-states (x1) (presento (cons x1 2) 1) )])
      (let ([sub (substitution-dict (state-substitution s))])
	(printf "~s~%~s~%" (map (lambda (p) (cons (make-var (- (sbral-length sub) (car p))) (cdr p))) (sbral->alist sub)) s)))

    
    (tassert "presento ground succeed" (run1 () (presento 1 1)) '())
    (tassert "presento ground fail" (run1 () (presento 2 1)) (void))
    (tassert "presento bound ground term succeed" (run1 (x1) (== x1 1) (presento x1 1)) 1)
    (tassert "presento bound ground term fail" (run1 (x1) (== x1 1) (presento x1 2)) (void))
    (tassert "presento fire ground term succeed" (run1 (x1) (presento x1 1) (== x1 1)) 1)
    (tassert "presento fire ground term fail" (run1 (x1) (presento x1 2) (== x1 1)) (void))
    
    (tassert "presento ground car succeed" (run1 () (presento (cons 1 2) 1)) '())
    (tassert "presento ground car fail" (run1 () (presento (cons 2 2) 1)) (void))
    (tassert "presento bound ground car succeed" (run1 (x1) (== x1 '(1)) (presento x1 1)) '(1))
    (tassert "presento bound ground car fail" (run1 (x1) (== x1 '(1)) (presento x1 2)) (void))
    (tassert "presento fire ground car succeed" (run1 (x1) (presento x1 1) (== x1 '(1))) '(1))
    (tassert "presento fire ground car fail" (run1 (x1) (presento x1 2) (== x1 '(1))) (void))

    (tassert "presento ground cdr succeed" (run1 () (presento (cons 2 1) 1)) '())    
    (tassert "presento ground cdr fail" (run1 () (presento (cons 2 2) 1)) (void))
    (tassert "presento bound ground cdr succeed" (run1 (x1) (== x1 '(2 . 1)) (presento x1 1)) '(2 . 1))
    (tassert "presento bound ground cdr fail" (run1 (x1) (== x1 '(2 . 2)) (presento x1 1)) (void))
    (tassert "presento fire ground cdr succeed" (run1 (x1) (presento x1 1) (== x1 '(2 . 1))) '(2 . 1))
    (tassert "presento fire ground cdr fail" (run1 (x1) (presento x1 3) (== x1 '(2 . 1))) (void))

    (tassert "presento fuzz fail" (run1 (x1) (presento (list 2 (list 2 (cons 2 (cons 2 (cons 2 x1))))) 1) (== x1 2)) (void))
    ;;(tassert "presento fuzz succeed" (run1 (x1) (presento (list 2 (list 3 (cons 4 (cons 5 (cons 6 x1))))) 1) ) 1)


    ;;(tassert "presento fuzz succeed" (run1 (x1) (presento (list 2 (list 2 (cons (list 2 2) (list 2 (cons x1 2) 2)) 2) 2) 1) (== x1 1)) 1)

    
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

					;(display (check-constraints (run-stream-constraint (make-noto (== x2 2)) empty-state) (== x2 2)))
    ;;(display (list-values (run-goal (disj* (== x1 x2) (== x1 2)) (unify empty-state x1 1) empty-package)))

					;(display "START\n")
    


    #;
    (tassert "fresh constraint increments varid bind incomplete"
	     (state-varid (values-ref (run-goal (constrain
						 (fresh (x1) 
						   (fresh (x2) (=/= x2 2))
						   (=/= x1 1))) empty-state empty-package) 1)) 3)


    (let ([s (run1-states (x1) (constrain (== x1 1)))])
      (tassert "constraint == store" (reify s x1) 1)
      (tassert "constraint == vid" (state-varid s) 2))
    (let ([s (run1-states (x1) (constrain (fresh (x2) (== x1 1))))])
      (tassert "constraint frash == store" (reify s x1) 1)
      (tassert "constraint fresh == vid" (state-varid s) 3))
    (let ([s (run1-states (x1 x2) (constrain (== x1 1) (== x2 2)))])
      (tassert "constraint conj == store" (reify s (cons x1 x2)) (cons 1 2))
      (tassert "constraint conj == vid" (state-varid s) 3))
    (let ([s (run1-states (x1) (constrain fail (== x1 1)))])
      (tassert "constraint bind fail" s failure))
    (let ([s (run1-states (x1) (constrain (== x1 1) (fresh (x2) (fresh (x3) (== x1 1)))))])
      (tassert "constraint bind store" (reify s x1) 1)
      (tassert "constraint bind vid" (state-varid s) 2))
    (let ([s (run1-states (x1) (constrain (conde [succeed] [succeed])))])      
      (tassert "constraint disj succeed store" (reify s x1) x1)
      (tassert "constraint disj succeed vid" (state-varid s) 2))
    (tassert "constraint disj =="
	     (run1 (x1 x2) (constrain (conde [(== x2 1)] [(== x2 2)]))
		   (constrain (conde [(== x1 1)] [(== x1 2)]))
		   (== x2 2))
	     (list (disj* (== x1 1) (== x1 2)) 2))
    (tassert "constraint disj lazy" (run1 (x1) (constrain (conde [(== x1 1)] [stale]))) (disj* (== x1 1) stale))
    (let ([s (run1-states (x1) (constrain (fresh (x2) succeed) (conde [(fresh (x3 x4) succeed)] [stale])))])      
      (tassert "constraint conj disj store" (reify s x1) x1)
      (tassert "constraint conj disj vid" (state-varid s) 2))

    (tassert "constraint disj conj"
	     (run1 (x1 x2) (constrain (conde [(== x1 1) (== x2 1)] [(== x1 2) (== x2 2)])))
	     (list (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2)))
		   (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2)))))
    

    #;
    (let ([s (run1-states (x1 x2) (constrain (conde [(fresh (x3) (== x1 1))] [(fresh (x3 x4) (== x2 2))])))])
      (tassert "constraint disj fresh store" (reify s (cons x1 x2)) (cons (disj* (== x1 1) (== x2 2))  x2))
      (tassert "constraint disj fresh vid" (state-varid s) 5))




#;
    (let ([s (run1-states (x1 x2) (constrain (fresh (x3) (== x2 2) (conde [(fresh (x3) (== x1 1))] [(fresh (x3) (== x1 2))]))))])
      (tassert "constraint disj bind complete store" (reify s (cons x1 x2)) 'unk)
      (tassert "constraint disj bind complete vid" (state-varid s) 4))
    
    #;
    (let ([s (run1-states (x1 x2) (constrain (conde [(== x1 1)] [(== x1 2)]) (fresh (x3) (== x2 2))))])
      (tassert "constraint disj bind complete store" (reify s (cons x1 x2)) 'unk)
      (tassert "constraint disj bind complete vid" (state-varid s) 4))


    ;;TODO test multi-success disj that should succeed instead of suspending as constraint. maybe normalize before starting constraint walk. maybe already handled by normalizing resulting constraint


;;    (tassert "presento fuzz succeed" (run1 (x1) (presento (cons (list 2 3 4 5 x1 ) 6) 1) (== x1 1)) 1)


    
    
#;
    (let ([c (run1 (x1) (presento (cons (list 2 3 4 5 x1 ) 6) 1))]
	  [s (unify empty-state x1 1)])
      ;;(pretty-print c)
      ;;(pretty-print s)
;      (pretty-print c)
 ;     (pretty-print (list-values (simplify-constraint c s)))
      #;
      (pretty-print (car  (disj-disjuncts c)))

      #;
      (pretty-print
       (check-constraints (state-add-constraint s x1 c) (== x1 1) ))

      (pretty-print
       (check-constraints
	(check-constraints (state-add-constraint s x1 c) (== x1 1) ) (== (make-var 4) 2))))
    
    ))
