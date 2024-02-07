
;;TODO test multi-success disj that should succeed instead of suspending as constraint. maybe normalize before starting constraint walk. maybe already handled by normalizing resulting constraint
(library (constraints-tests)
  (export run-constraints-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (utils) (state) (constraints))

  (define (forever x)
    (fresh (y) (forever x)))

  (define (run-constraints-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))
    (define x4 (make-var 4))
    (define stale (lambda (s p) (cert #f))) ; Fresh that should never be expanded

    ;; === VARID ===
    (let ([s (run1-state (x1) (constraint (== x1 1)))])
      (tassert "constraint == store" (reify s x1) 1)
      (tassert "constraint == vid" (state-varid s) 2))
    #;
    (let ([s (run1-state (x1) (constraint (fresh (x2) (== x1 1))))]) ;
    (tassert "constraint frash == store" (reify s x1) 1) ;
    (tassert "constraint fresh == vid" (state-varid s) 3))
    (let ([s (run1-state (x1 x2) (constraint (== x1 1) (== x2 2)))])
      (tassert "constraint conj == store" (reify s (cons x1 x2)) (cons 1 2))
      (tassert "constraint conj == vid" (state-varid s) 3))
    (let ([s (run1-state (x1) (constraint fail (== x1 1)))])
      (tassert "constraint bind fail" s failure))
    #;
    (let ([s (run1-state (x1) (constraint (== x1 1) (fresh (x2) (fresh (x3) (== x1 1)))))]) ;
    (tassert "constraint bind store" (reify s x1) 1) ;
    (tassert "constraint bind vid" (state-varid s) 2))
    (let ([s (run1-state (x1) (constraint (conde [succeed] [succeed])))])
      (tassert "constraint disj succeed store" (reify s x1) x1)
      (tassert "constraint disj succeed vid" (state-varid s) 2))

    #;
    (tassert "constraint disj =="
	     (run1 (x1 x2) (constraint (conde [(== x2 1)] [(== x2 2)]))
		   (constraint (conde [(== x1 1)] [(== x1 2)]))
		   (== x2 2))
    (list (disj* (== x1 1) (== x1 2)) 2))
    #;
    (tassert "constraint disj lazy" (run1 (x1) (constraint (conde [(== x1 1)] [(== x1 2)] [stale]))) (disj* (== x1 1) (== x1 2) stale))


    #;
    (let ([s (run1-state (x1) (constraint (fresh (x2) succeed) (conde [(fresh (x3 x4) succeed)] [stale])))]) ;
    (tassert "constraint conj disj store" (reify s x1) x1) ;
    (tassert "constraint conj disj vid" (state-varid s) 2))


    #;
    (tassert "constraint disj conj"
	     (run1 (x1 x2) (constraint (conde [(== x1 1) (== x2 1)] [(== x1 2) (== x2 2)])))
	     (list (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2)))
		   (disj* (conj* (== x1 1) (== x2 1)) (conj* (== x1 2) (== x2 2)))))

    ;; === BOOLEANO ===

    (tassert "booleano ground t" (run1 () (booleano #t)) '())
    (tassert "booleano ground f" (run1 () (booleano #f)) '())
    (tassert "booleano ground undecidable" (run1 () (booleano 'undecidable)) (void))
    (tassert "booleano free t" (run1 (x1) (booleano x1)) (disj (== x1 #t) (== x1 #f)))

    (tassert "booleano bound t" (run1 (x1) (== x1 #t) (booleano x1)) #t)
    (tassert "booleano bound f" (run1 (x1) (== x1 #f) (booleano x1)) #f)
    (tassert "booleano bound undecidable fail" (run1 (x1) (== x1 'undecidable) (booleano x1)) (void))
    (tassert "booleano fired t" (run1 (x1) (booleano x1) (== x1 #t)) #t)
    (tassert "booleano fired f" (run1 (x1) (booleano x1) (== x1 #f)) #f)
    (tassert "booleano fired undecidable fail" (run1 (x1) (booleano x1) (== x1 'undecidable)) (void))
    (tassert "booleano unsatisfiable with all-diff" (run1 (x1 x2 x3) (=/= x1 x2) (=/= x2 x3) (=/= x1 x3) (booleano x1) (booleano x2) (booleano x3)) (void)) ; TODO to allow =/= to suspend on single variable, disj must put proxies on any vars that would be touched by its disjuncts so they can rerun the disjunction

    ;; === LISTO ===

    (tassert "listo ground number" (run1 () (listo 1)) (void))
    (tassert "listo ground 1-list" (run1 () (listo '(1))) '())
    (tassert "listo ground 2-list" (run1 () (listo '(1 2))) '())
    (tassert "listo ground 3-list" (run1 () (listo '(1 2 3))) '())
    (tassert "listo ground improper 1-list" (run1 () (listo '(1 . 2))) (void))
    (tassert "listo ground improper 2-list" (run1 () (listo '(1 2 . 3))) (void))
    (tassert "listo ground improper 3-list" (run1 () (listo '(1 2 3 . 4))) (void))

    (tassert "listo bound number" (run1 (x1) (== x1 1) (listo x1)) (void))
    (tassert "listo bound 1-list" (run1 (x1) (== x1 '(1)) (listo x1)) '(1))
    (tassert "listo bound 2-list" (run1 (x1) (== x1 '(1 2)) (listo x1)) '(1 2))
    (tassert "listo bound 3-list" (run1 (x1) (== x1 '(1 2 3)) (listo x1)) '(1 2 3))
    (tassert "listo bound improper 1-list" (run1 (x1) (== x1 '(1 . 2)) (listo x1)) (void))
    (tassert "listo bound improper 2-list" (run1 (x1) (== x1 '(1 2 . 3)) (listo x1)) (void))
    (tassert "listo bound improper 3-list" (run1 (x1) (== x1 '(1 2 3 . 4)) (listo x1)) (void))

    (tassert "listo fired number" (run1 (x1) (listo x1) (== x1 1)) (void))
    (tassert "listo fired 1-list" (run1 (x1) (listo x1) (== x1 '(1))) '(1))
    (tassert "listo fired 2-list" (run1 (x1) (listo x1) (== x1 '(1 2))) '(1 2))
    (tassert "listo fired 3-list" (run1 (x1) (listo x1) (== x1 '(1 2 3))) '(1 2 3))
    (tassert "listo fired improper 1-list" (run1 (x1) (listo x1) (== x1 '(1 . 2))) (void))
    (tassert "listo fired improper 2-list" (run1 (x1) (listo x1) (== x1 '(1 2 . 3))) (void))
    (tassert "listo fired improper 3-list" (run1 (x1) (listo x1) (== x1 '(1 2 3 . 4))) (void))

    (tassert "noto listo ground number" (run1 () (noto (listo 1))) '())
    (tassert "noto listo ground nil" (run1 () (noto (listo '()))) (void))
    (tassert "noto listo ground pair" (run1 () (noto (listo '(1 . 2)))) '())
    (tassert "noto listo ground 1-list" (run1 () (noto (listo '(1)))) (void))

    #;    (tassert "listo multihop 3-list" (run1 (x1) (listo x1) (fresh (x2 x3 x4) (== x1 x2) (== x2 (cons 1 x3)) (== x3 (cons 2 x4)) (== x4 (list 3)))) '(1 2 3))
    #;    (tassert "listo multihop improper 3-list" (run1 (x1) (listo x1) (fresh (x2 x3 x4) (== x1 x2) (== x2 (cons 1 x3)) (== x3 (cons 2 x4)) (== x4 '(3 . 4)))) (void))

    ;; === FINITE DOMAIN ===

    (tassert "finite domain ground succeed 1" (run1 () (finite-domain 1 '(1 2 3))) '())
    (tassert "finite domain ground succeed 2" (run1 () (finite-domain 2 '(1 2 3))) '())
    (tassert "finite domain ground succeed 3" (run1 () (finite-domain 3 '(1 2 3))) '())
    (tassert "finite domain ground fail 3" (run1 () (finite-domain 4 '(1 2 3))) (void))

    (tassert "finite domain free" (run1 (x1) (finite-domain x1 '(1 2 3))) (disj (== x1 1) (disj (== x1 2) (== x1 3))))

    (tassert "finite domain bound succeed" (run1 (x1) (== x1 2) (finite-domain x1 '(1 2 3))) 2)
    (tassert "finite domain bound fail" (run1 (x1) (== x1 4) (finite-domain x1 '(1 2 3))) (void))

    (tassert "finite domain fired succeed" (run1 (x1) (finite-domain x1 '(1 2 3)) (== x1 2)) 2)
    (tassert "finite domain fired fail" (run1 (x1) (finite-domain x1 '(1 2 3)) (== x1 4)) (void))

    ;; === IMPLIES ===

    (tassert "implies consequent true" (run1 (x1 x2) (==> (== x1 1) (== x2 2)) (== x2 2)) (list (disj (=/= x1 1) (== x2 2)) 2))
    (tassert "implies consequent false" (run1 (x1 x2) (==> (== x1 1) (== x2 2)) (== x2 3)) (list (disj* (=/= x1 1) (== x2 2)) 3))
    #;
    (#(conj
    (#(disj (#(conj (#(noto #(== #(var 1) 1))
    #(== #(var 2) 2)))
    #(== #(var 2) 2)))
    #(disj (#(noto #(== #(var 1) 1))
    #(== #(var 2) 2))))) 2)

    ;; === SYMBOLO ===
    (tassert "symbolo simplifies succeed" (symbolo 'symbol) succeed)
    (tassert "symbolo simplifies fail" (symbolo 42) fail)

    (tassert "symbolo ground succeed" (run1 () (symbolo 'symbol)) '())
    (tassert "symbolo ground fail" (run1 () (symbolo 42)) (void))

    (tassert "symbolo bound succeed" (run1 (x1) (== x1 'symbol) (symbolo x1)) 'symbol)
    (tassert "symbolo bound fail" (run1 (x1) (== x1 42) (symbolo x1)) (void))

    (tassert "symbolo fire succeed" (run1 (x1) (symbolo x1) (== x1 'symbol)) 'symbol)
    (tassert "symbolo fire fail" (run1 (x1) (symbolo x1) (== x1 42)) (void))

    (tassert "not symbolo ground fail" (run1 () (noto (symbolo 'symbol))) (void))
    (tassert "not symbolo ground succeed" (run1 () (noto (symbolo 42))) '())

    (tassert "not symbolo bound fail" (run1 (x1) (== x1 'symbol) (noto (symbolo x1))) (void))
    (tassert "not symbolo bound succeed" (run1 (x1) (== x1 42) (noto (symbolo x1))) 42)

    (tassert "not symbolo fire fail" (run1 (x1) (noto (symbolo x1)) (== x1 'symbol)) (void))
    (tassert "not symbolo fire succeed" (run1 (x1) (noto (symbolo x1)) (== x1 42)) 42)
    (tassert "noto does not mangle ctn" (run1 (x1) (constraint (noto (symbolo x1)) (matcho ([x1 (1 2)]))) (== x1 '(1 2))) '(1 2))

    (tassert "symbolo-symbolo succeed" (run1 (x1) (symbolo x1) (symbolo x1)) (symbolo x1))
    (tassert "symbolo-numbero fail" (run1 (x1) (symbolo x1) (numbero x1)) (void))

    (tassert "pconstraints fully walk attr vars" (run1 (x1 x2) (== x1 x2) (symbolo x1) (symbolo x1)) (list (symbolo x2) (symbolo x2)))
    
    ;; === PLUSO ===

    ;;(tassert "pluso ground 1" (run1 () (pluso 42)) '())

    ;; === ABSENTO ===

    (tassert "absento ground cdr fail" (run1 () (absento 1  (cons 2 1))) (void))
    (tassert "absento ground fail" (run1 () (absento 1 1)) (void))
    (tassert "absento ground succeed" (run1 () (absento 1 2)) '())
    (tassert "absento bound ground term fail" (run1 (x1) (== x1 1) (absento 1 x1)) (void))
    (tassert "absento bound ground term succeed" (run1 (x1) (== x1 1) (absento 2 x1)) 1)
    (tassert "absento fire ground term fail" (run1 (x1) (absento 1 x1) (== x1 1)) (void))
    (tassert "absento fire ground term succeed" (run1 (x1) (absento 2 x1) (== x1 1)) 1)

    (tassert "absento ground car fail" (run1 () (absento 1 (cons 1 2))) (void))
    (tassert "absento ground car succeed" (run1 () (absento 1 (cons 2 2))) '())
    (tassert "absento bound car fail" (run1 (x1) (== x1 '(1)) (absento 1 x1)) (void))
    (tassert "absento bound car succeed" (run1 (x1) (== x1 '(1)) (absento 2 x1)) '(1))
    (tassert "absento fire car fail" (run1 (x1) (absento 1 x1) (== x1 '(1))) (void))
    (tassert "absento fire car succeed" (run1 (x1) (absento 2 x1) (== x1 '(1))) '(1))

    (tassert "absento ground cdr fail" (run1 () (absento 1 (cons 2 1))) (void))
    (tassert "absento ground cdr succeed" (run1 () (absento 1 (cons 2 2))) '())
    (tassert "absento bound cdr fail" (run1 (x1) (== x1 '(2 . 1)) (absento 1 x1)) (void))
    (tassert "absento bound cdr succeed" (run1 (x1) (== x1 '(2 . 2)) (absento 1 x1)) '(2 . 2))
    (tassert "absento fire cdr fail" (run1 (x1) (absento 1 x1) (== x1 '(2 . 1))) (void))
    (tassert "absento fire cdr succeed" (run1 (x1) (absento 3 x1) (== x1 '(2 . 1))) '(2 . 1))

    (tassert "absento hangs if matcho generates free vars in constraint"
	     (run1 (x0 x1 x2 x3)
		   (absento 100 x0) (== x0 (cons 0 x1)) (== x1 (cons 1 x2)) (== x2 (cons 2 x3)) (== x3 3)) '((0 1 2 . 3) (1 2 . 3) (2 . 3) 3))

    (tassert "absento hangs on this due to bad return condition in solve-disj"
	     (run1 (x1 x2 x3 x4 x5)
		   (absento 100 x1) (== x1 (cons 1 x2)) (== x2 (cons 2 x3)) (== x3 (cons 3 x4)) (== x4 (cons 4 x5)) (== x5 '(5))) '((1 2 3 4 5) (2 3 4 5) (3 4 5) (4 5) (5)))


    (tassert "duplicate absento simplifies down to duplicate matchos"
	     (cdr (run1 (x1 x2 x3) (absento 1 x1) (absento 2 x1) (== x1 (cons x2 x3))))
	     (lambda (g)
	       (let ([m21 (disj-rhs (conj-rhs (conj-lhs (car g))))]
		     [m22 (conj-rhs (conj-rhs (car g)))]
		     [m31 (disj-rhs (conj-rhs (conj-lhs (cadr g))))]
		     [m32 (conj-rhs (conj-rhs (cadr g)))])
		 (equal? g (list
			    (conj (conj (=/= x2 1) (disj (conj (=/= x2 2) (noto (pairo x2))) m21))
				  (disj (noto (pairo x2)) m22))
			    (conj (conj (=/= x3 1) (disj (conj (=/= x3 2) (noto (pairo x3))) m31))
				  (disj (noto (pairo x3)) m32)))))))

    ;; === PRESENTO ===

    (tassert "presento unbound term succeed" (run1 (x1) (presento 1 x1) (== x1 1)) 1)
    (tassert "presento unbound term fail" (run1 (x1) (presento 1 x1) (== x1 2)) (void))
    (tassert "presento unbound term" (run1 (x1) (presento 1 x1)) (lambda (a) (and (disj? a) (equal? (disj-lhs a) (== x1 1)) (matcho? (disj-rhs a)))))

    (tassert "presento ground succeed" (run1 () (presento 1 1)) '())
    (tassert "presento ground fail" (run1 () (presento 1 2)) (void))
    (tassert "presento bound ground term succeed" (run1 (x1) (== x1 1) (presento 1 x1)) 1)
    (tassert "presento bound ground term fail" (run1 (x1) (== x1 1) (presento 2 x1)) (void))
    (tassert "presento fire ground term succeed" (run1 (x1) (presento 1 x1) (== x1 1)) 1)
    (tassert "presento fire ground term fail" (run1 (x1) (presento 2 x1) (== x1 1)) (void))

    (tassert "presento ground car succeed" (run1 () (presento 1 (cons 1 2))) '())
    (tassert "presento ground car fail" (run1 () (presento 1 (cons 2 2))) (void))
    (tassert "presento bound ground car succeed" (run1 (x1) (== x1 '(1)) (presento 1 x1)) '(1))
    (tassert "presento bound ground car fail" (run1 (x1) (== x1 '(1)) (presento 2 x1)) (void))
    (tassert "presento fire ground car succeed" (run1 (x1) (presento 1 x1) (== x1 '(1))) '(1))
    (tassert "presento fire ground car fail" (run1 (x1) (presento 2 x1) (== x1 '(1))) (void))

    (tassert "presento ground cdr succeed" (run1 () (presento 1 (cons 2 1))) '())
    (tassert "presento ground cdr fail" (run1 () (presento 1 (cons 2 2))) (void))
    (tassert "presento bound ground cdr succeed" (run1 (x1) (== x1 '(2 . 1)) (presento 1 x1)) '(2 . 1))
    (tassert "presento bound ground cdr fail" (run1 (x1) (== x1 '(2 . 2)) (presento 1 x1)) (void))
    (tassert "presento fire ground cdr succeed" (run1 (x1) (presento 1 x1) (== x1 '(2 . 1))) '(2 . 1))
    (tassert "presento fire ground cdr fail" (run1 (x1) (presento 3 x1) (== x1 '(2 . 1))) (void))

    (tassert "presento fuzz fail" (run1 (x1) (presento 1 (list 2 (list 2 (cons 2 (cons 2 (cons 2 x1)))))) (== x1 2)) (void))

    ;; This structure triggered a larger constraint cascade even than seemingly more complex structures. 
    (tassert "presento fuzz succeed ground" (run1 (x1) (presento 1 (cons (list 2 3 4 5 1) 6))) x1)
    (tassert "presento fuzz succeed bound" (run1 (x1) (== x1 1) (presento 1 (cons (list 2 3 4 5 x1) 6))) 1)
    (tassert "presento fuzz succeed fired" (run1 (x1) (presento 1 (cons (list 2 3 4 5 x1 ) 6)) (== x1 1)) 1)
    (tassert "presento fuzz fail ground" (run1 (x1) (presento 1 (cons (list 2 3 4 5 7) 6))) (void))
    (tassert "presento fuzz fail bound" (run1 (x1) (== x1 7) (presento 1 (cons (list 2 3 4 5 x1) 6))) (void))
    (tassert "presento fuzz fail fired" (run1 (x1) (presento 1 (cons (list 2 3 4 5 x1 ) 6)) (== x1 7)) (void))

    (tassert "noto presento ground cdr fail" (run1 () (noto (presento 1  (cons 2 1)))) (void))
    (tassert "noto presento ground fail" (run1 () (noto (presento 1 1))) (void))
    (tassert "noto presento ground succeed" (run1 () (noto (presento 1 2))) '())
    (tassert "noto presento bound ground term fail" (run1 (x1) (== x1 1) (noto (presento 1 x1))) (void))
    (tassert "noto presento bound ground term succeed" (run1 (x1) (== x1 1) (noto (presento 2 x1))) 1)
    (tassert "noto presento fire ground term fail" (run1 (x1) (noto (presento 1 x1)) (== x1 1)) (void))
    (tassert "noto presento fire ground term succeed" (run1 (x1) (noto (presento 2 x1)) (== x1 1)) 1)

    (tassert "noto presento ground car fail" (run1 () (noto (presento 1 (cons 1 2)))) (void))
    (tassert "noto presento ground car succeed" (run1 () (noto (presento 1 (cons 2 2)))) '())
    (tassert "noto presento bound car fail" (run1 (x1) (== x1 '(1)) (noto (presento 1 x1))) (void))
    (tassert "noto presento bound car succeed" (run1 (x1) (== x1 '(1)) (noto (presento 2 x1))) '(1))
    (tassert "noto presento fire car fail" (run1 (x1) (noto (presento 1 x1)) (== x1 '(1))) (void))
    (tassert "noto presento fire car succeed" (run1 (x1) (noto (presento 2 x1)) (== x1 '(1))) '(1))

    (tassert "noto presento ground cdr fail" (run1 () (noto (presento 1 (cons 2 1)))) (void))
    (tassert "noto presento ground cdr succeed" (run1 () (noto (presento 1 (cons 2 2)))) '())
    (tassert "noto presento bound cdr fail" (run1 (x1) (== x1 '(2 . 1)) (noto (presento 1 x1))) (void))
    (tassert "noto presento bound cdr succeed" (run1 (x1) (== x1 '(2 . 2)) (noto (presento 1 x1))) '(2 . 2))
    (tassert "noto presento fire cdr fail" (run1 (x1) (noto (presento 1 x1)) (== x1 '(2 . 1))) (void))
    (tassert "noto presento fire cdr succeed" (run1 (x1) (noto (presento 3 x1)) (== x1 '(2 . 1))) '(2 . 1))

    (tassert "noto presento hangs if matcho generates free vars in constraint"
	     (run1 (x0 x1 x2 x3)
		   (noto (presento 100 x0)) (== x0 (cons 0 x1)) (== x1 (cons 1 x2)) (== x2 (cons 2 x3)) (== x3 3)) '((0 1 2 . 3) (1 2 . 3) (2 . 3) 3))

    (tassert "noto presento hangs on this due to bad return condition in solve-disj"
	     (run1 (x1 x2 x3 x4 x5)
		   (noto (presento 100 x1)) (== x1 (cons 1 x2)) (== x2 (cons 2 x3)) (== x3 (cons 3 x4)) (== x4 (cons 4 x5)) (== x5 '(5))) '((1 2 3 4 5) (2 3 4 5) (3 4 5) (4 5) (5)))

    (tassert "noto presento found by generative test" (run1 (x1 x2) (noto (presento x2 `((,x2) ,x1 . ,x1))) (== x1 1)) (void))
    
    #;;TODO test that recursive disjunctions containing unifications dont run forever looking for a case that doesn't involve == when attributing/solving disjunctions
    (tassert "presento free" (run1 (x1 x2) (presento x1 x2)) (lambda (a) (and (car a))))
    #;
    (tassert "presento free reverse" (run1 (x1 x2) (presento x2 x1)) 1)






    ;; === FILTERO ===

    (tassert "filtero null" (run* (q) (filtero (lambda (x) succeed) '() q)) '(()))
    (tassert "filtero succeed" (run* (q) (filtero (lambda (x) succeed) '(1 2 3) q)) '((1 2 3)))
    (tassert "filtero fail" (run* (q) (filtero (lambda (x) fail) '(1 2 3) q)) '(()))
    (tassert "filtero ==" (run* (q) (filtero (lambda (x) (== x 2)) '(1 2 3) q)) '((2)))
    (tassert "filtero |" (run* (q) (filtero (lambda (x) (disj (== x 2) (== x 3))) '(1 2 3) q)) '((2 3)))
#;
    (parameterize ([lazy-solver #f])
      (tassert "filtero free" (run* (q x) (filtero (lambda (x) (disj (== x 2) (== x 3))) `(1 ,x 3) q) (== x 3)) '((3 3))))
    
    ))
