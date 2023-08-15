(library (reducer-tests) ; Tests the core mechanisms of the constraint solver
  (export run-reducer-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes) (utils) (state) (solver))
  
  (define (run-reducer-tests)
    (define x1 (make-var 1))
    (define x2 (make-var 2))
    (define x3 (make-var 3))
    (define x4 (make-var 4))


    ;; === EQUALITY ===

    (let ([s (list (cons x1 1))]
	  [s-free (list (cons x1 x2))]
	  [s-pair (list (cons x1 (cons x2 x3)))])
      
      (tassert "reduce == & ==" (simplify-unification (== x1 1) s) (list succeed succeed))
      (tassert "reduce == & ==!" (simplify-unification (== x1 2) s) (list fail fail))
      (tassert "reduce == & ==?" (simplify-unification (== x1 x2) s) (list (== x2 1) succeed))
      (tassert "reduce == & ?==" (simplify-unification (== x2 2) s) (list (== x2 2) succeed))
      (tassert "reduce == & ^==" (simplify-unification (== x2 2) s-free) (list (== x2 2) succeed))
      (tassert "reduce == & ==*" (simplify-unification (== x1 '(2 . 3)) s-pair) (list (conj (== x3 3) (== x2 2)) succeed))
      (tassert "reduce == & ==!&==" (simplify-unification (conj (== x1 2) (== x1 1)) s) (list fail fail))
      (tassert "reduce == & ==&==!" (simplify-unification (conj (== x1 1) (== x1 2)) s) (list fail fail))

      (tassert "reduce == & =/=" (simplify-unification (=/= x1 1) s) (list fail succeed))
      (tassert "reduce == & =/=!" (simplify-unification (=/= x1 2) s) (list succeed succeed))
      (tassert "reduce == & =/=?" (simplify-unification (=/= x1 1) s-free) (list (=/= x2 1) succeed))

      (tassert "reduce == & satisfied" (simplify-unification (numbero x1) s) (list succeed succeed))
      (tassert "reduce == & not satisfied" (simplify-unification (noto (numbero x1)) s) (list fail succeed))
      (tassert "reduce == & unsatisfiable" (simplify-unification (symbolo x1) s) (list fail fail))
      (tassert "reduce == & not unsatisfiable" (simplify-unification (noto (symbolo x1)) s) (list succeed succeed))
      (tassert "reduce == & undecidable" (simplify-unification (symbolo x2) s) (list (symbolo x2) succeed))
      (tassert "reduce == & not undecidable" (simplify-unification (noto (symbolo x2)) s) (list (noto (symbolo x2)) succeed))
      (tassert "reduce ==f & undecidable" (simplify-unification (symbolo x1) s-free) (list (symbolo x2) succeed))
      (tassert "reduce ==f & not undecidable" (simplify-unification (noto (symbolo x1)) s-free) (list (noto (symbolo x2)) succeed))

      (tassert "reduce == & matcho fail" (simplify-unification (matcho ([x1 (a . d)])) s) (list fail fail))
      (tassert "reduce == & matcho simplified" (simplify-unification (matcho ([x1 (a . d)])) s-free) (lambda (g) (and (succeed? (cadr g)) (matcho? (car g)) (eq? x2 (car (matcho-out-vars (car g)))))))
      (tassert "reduce == & matcho recheck" (simplify-unification (matcho ([x1 (a . d)] [x2 (b . c)])) `((,x1 . (1 . 2)) (,x2 . (3 . 4)))) (lambda (g) (and (succeed? (car g)) (matcho? (cadr g)) (null? (matcho-out-vars (cadr g))) (equal? '((3 . 4) (1 . 2)) (matcho-in-vars (cadr g))))))
      (tassert "reduce == & not matcho succeed" (simplify-unification (noto (matcho ([x1 (a . d)]))) s) (list succeed succeed))
      (tassert "reduce == & not matcho simplified" (simplify-unification (noto (matcho ([x1 (a . d)]))) s-free) (lambda (g) (and (succeed? (cadr g)) (noto? (car g)) (matcho? (noto-goal (car g))) (eq? x2 (car (matcho-out-vars (noto-goal (car g))))))))
      (tassert "reduce == & not matcho recheck" (simplify-unification (noto (matcho ([x1 (a . d)] [x2 (b . c)]))) `((,x1 . (1 . 2)) (,x2 . (3 . 4)))) (lambda (g) (and (succeed? (car g)) (noto? (cadr g)) (matcho? (noto-goal (cadr g))) (null? (matcho-out-vars (noto-goal (cadr g)))) (equal? '((3 . 4) (1 . 2)) (matcho-in-vars (noto-goal (cadr g)))))))
      (tassert "reduce == & ==!&==?" (simplify-unification (disj (== x1 2) (== x2 3)) s) (list succeed (== x2 3)))
      (tassert "reduce == & ==?&==?" (simplify-unification (disj (== x2 2) (== x2 3)) s) (list (disj (== x2 2) (== x2 3)) succeed))
      (tassert "reduce == & matcho|unsatisfiablel" (simplify-unification (disj (matcho ([x1 (a . d)]) (== a 1) (== d 2)) (=/= x1 (cons x2 x3))) s-pair) (lambda (s-r) (and (succeed? (car s-r)) (matcho? (list-ref s-r 1)))))
      (tassert "reduce == & =/=|unsatisfiable|undecidable" (simplify-unification (disj (disj (=/= x2 2) (=/= x1 1)) (== x2 2)) s) (list (disj (=/= x2 2) (== x2 2)) succeed)))

    ;; === DISEQUALITY ===
    (tassert "== succeed" (simplify-=/= (== x1 1) x1 1 (=/= x1 1)) (list succeed fail succeed (=/= x1 1)))
    (tassert "== undecidable" (simplify-=/= (== x1 (cons x2 x3)) x1 (cons x3 x2) (=/= x1 1)) (list (== x1 (cons x2 x3)) (== x1 (cons x2 x3)) succeed (=/= x1 1)))
    (tassert "=/= undecidable" (simplify-=/= (=/= x1 (cons x2 x3)) x1 (cons x3 x2) (=/= x1 1)) (list (=/= x1 (cons x2 x3)) (=/= x1 (cons x2 x3)) succeed (=/= x1 1)))
    (tassert "symbolo fail" (simplify-=/= (symbolo x1) x1 1 (=/= x1 1)) (list fail (symbolo x1) succeed (=/= x1 1)))
    (tassert "symbolo2 undecidable" (simplify-=/= (symbolo x1) x2 1 (=/= x1 1)) (list (symbolo x1) (symbolo x1) succeed (=/= x1 1)))
    (tassert "not numbero fail" (simplify-=/= (noto (numbero x1)) x1 1 (=/= x1 1)) (list fail (noto (numbero x1)) succeed (=/= x1 1)))
    (tassert "=/= fail" (simplify-=/= (=/= x1 1) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= succeed" (simplify-=/= (=/= x1 2) x1 1 (=/= x1 1)) (list succeed (=/= x1 2) succeed (=/= x1 1)))
    (tassert "conj fail" (simplify-=/= (conj (== x1 1) (=/= x1 1)) x1 1 (=/= x1 1)) (list fail fail succeed (=/= x1 1)))
    (tassert "matcho fail" (simplify-=/= (matcho ([x1 (a . d)])) x1 1 (=/= x1 1)) (lambda (a) (and (fail? (list-ref a 0)) (matcho? (list-ref a 1)) (equal? (cddr a) (list succeed (=/= x1 1))))))
    (tassert "matcho2 undecidable" (simplify-=/= (matcho ([x1 (a . d)])) x2 1 (=/= x1 1)) (lambda (a) (and (matcho? (car a)) (matcho? (cadr a)) (succeed? (caddr a))) (=/= x1 1)))
    (tassert "not matcho succeed" (simplify-=/= (noto (matcho ([x1 (a . d)]))) x1 1 (=/= x1 1)) (lambda (a) (and (succeed? (car a)) (noto? (cadr a)) (succeed? (caddr a)) (equal? (cadddr a) (=/= x1 1)))))
    (tassert "matcho undecidable" (simplify-=/= (matcho ([x1 (a . d)])) x1 '(1 . 2) (=/= x1 1)) (lambda (a) (and (matcho? (car a)) (matcho? (cadr a)) (succeed? (caddr a))) (=/= x1 1)))
    (tassert "not matcho undecidable" (simplify-=/= (noto (matcho ([x1 (a . d)]))) x1 '(1 . 2) (=/= x1 '(1 . 2))) (lambda (a) (and (noto? (car a)) (noto? (cadr a)) (succeed? (caddr a))) (=/= x1 '(1 . 2))))
    (tassert "=/= satisfied|satisfies" (simplify-=/= (disj (=/= x1 1) (symbolo x1)) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= satisfies|satisfies" (simplify-=/= (disj (symbolo x1) (symbolo x1)) x1 1 (=/= x1 1)) (list fail (symbolo x1) succeed succeed))
    (tassert "=/= satisfies|satisfied|unnormalized" (simplify-=/= (disj (=/= x1 1) (disj (symbolo x1) (=/= x2 2))) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= satisfied|satisfied|unnormalized" (simplify-=/= (disj (symbolo x1) (disj (symbolo x1) (=/= x2 2))) x1 1 (=/= x1 1)) (list (=/= x2 2) (disj (symbolo x1) (disj (symbolo x1) (conj (=/= x1 1) (=/= x2 2)))) succeed succeed))
    (tassert "=/= unsatisfiable|satisfied" (simplify-=/= (disj (== x1 1) (symbolo x1)) x1 1 (=/= x1 1)) (list succeed succeed (symbolo x1) succeed))
    (tassert "=/= satisfied|unsatisfiable" (simplify-=/= (disj (symbolo x1) (== x1 1)) x1 1 (=/= x1 1)) (list succeed (symbolo x1)  succeed succeed))
    (tassert "=/= satisfied|unsatisfiable|undecidable" (simplify-=/= (disj (symbolo x1) (disj (== x1 1) (=/= x1 2))) x1 1 (=/= x1 1)) (list succeed (disj (symbolo x1) (conj (=/= x1 1) (=/= x1 2))) succeed succeed))
    (tassert "=/= satisfied|undecidable" (simplify-=/= (disj (symbolo x1) (=/= x1 2)) x1 1 (=/= x1 1)) (list succeed (disj (symbolo x1) (conj (=/= x1 1) (=/= x1 2))) succeed succeed))
    (tassert "=/= unsatisfiable|undecidable" (simplify-=/= (disj (== x1 1) (=/= x1 2)) x1 1 (=/= x1 1)) (list succeed succeed (conj (=/= x1 1) (=/= x1 2)) succeed))
    (tassert "=/= undecidable|unsatisfiable" (simplify-=/= (disj (=/= x1 2) (== x1 1)) x1 1 (=/= x1 1)) (list succeed (conj (=/= x1 1) (=/= x1 2)) succeed succeed))
    (tassert "=/= undecidable|undecidable" (simplify-=/= (disj (=/= x1 2) (=/= x1 3)) x1 1 (=/= x1 1)) (list succeed (conj (=/= x1 1) (disj (=/= x1 2) (=/= x1 3))) succeed succeed))
    (tassert "=/= recheck|undecidable" (simplify-=/= (disj (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) x1 1 (=/= x1 1)) (list succeed succeed (disj (conj (=/= x2 2) (conj (=/= x1 1) (=/= x2 3))) (=/= x1 3)) succeed))
    (tassert "=/= satisfied|recheck" (simplify-=/= (disj (symbolo x1) (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3)))) x1 1 (=/= x1 1)) (list succeed (disj (symbolo x1) (conj (=/= x2 2) (conj (=/= x1 1) (=/= x2 3)))) succeed succeed))
    (tassert "=/= satisfies|undecidable" (simplify-=/= (disj (=/= x1 1) (=/= x1 2)) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= undecidable|satisfies" (simplify-=/= (disj (=/= x1 2) (=/= x1 1)) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= =/=^|=/=^|=/=" (simplify-=/= (disj (=/= x1 2) (disj (=/= x1 3) (=/= x1 1))) x1 1 (=/= x1 1)) (list fail succeed succeed (=/= x1 1)))
    (tassert "=/= ==^|==^|==" (simplify-=/= (disj (disj (== x1 2) (== x1 3)) (== x1 1)) x1 1 (=/= x1 1)) (list succeed (disj (== x1 2) (== x1 3)) succeed succeed))
    (tassert "=/= ==^|==^|==|==^" (simplify-=/= (disj (disj (disj (== x1 2) (== x1 3)) (== x1 1)) (== x1 4)) x1 1 (=/= x1 1)) (list succeed (disj (disj (== x1 2) (== x1 3)) (== x1 4)) succeed succeed))
    (tassert "=/= (recheck&recheck)|undecidable" (simplify-=/= (disj (conj (disj (== x1 1) (=/= x2 3)) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) x1 1 (=/= x1 1)) (list succeed succeed (disj (conj (conj (=/= x1 1) (=/= x2 3)) (=/= x2 3)) (=/= x1 3)) succeed))
    (tassert "=/= (satisfies|undecidable)|(satisfied|undecidable)" (simplify-=/= (disj (conj (=/= x1 2) (disj (=/= x1 1) (=/= x1 3))) (conj (=/= x1 4) (disj (symbolo x1) (=/= x1 5)))) x1 1 (=/= x1 1)) (list succeed (disj (=/= x1 2) (conj (=/= x1 4) (disj (symbolo x1) (conj (=/= x1 1) (=/= x1 5))))) succeed succeed))

    ;; === PCONSTRAINT ===
    (tassert "reduce pconstraint ==" (simplify-pconstraint (== x1 1) (numbero x1)) (list succeed (== x1 1) succeed (numbero x1)))
    (tassert "reduce pconstraint ==!" (simplify-pconstraint (== x1 'symbol) (numbero x1)) (list fail fail succeed (numbero x1)))
    (tassert "reduce pconstraint ?==" (simplify-pconstraint (== x2 1) (numbero x1)) (list (numbero x1) (== x2 1) succeed (numbero x1)))
    (tassert "reduce pconstraint ?==!" (simplify-pconstraint (== x2 'symbol) (numbero x1)) (list (numbero x1) (== x2 'symbol) succeed (numbero x1)))
    
    (tassert "reduce pconstraint =/=" (simplify-pconstraint (=/= x1 1) (numbero x1)) (list (numbero x1) (=/= x1 1) succeed (numbero x1)))
    (tassert "reduce pconstraint =/=!" (simplify-pconstraint (=/= x1 'symbol) (numbero x1)) (list (numbero x1) succeed succeed (numbero x1)))
    (tassert "reduce pconstraint ?==" (simplify-pconstraint (=/= x2 1) (numbero x1)) (list (numbero x1) (=/= x2 1) succeed (numbero x1)))
    (tassert "reduce pconstraint ?==!" (simplify-pconstraint (=/= x2 'symbol) (numbero x1)) (list (numbero x1) (=/= x2 'symbol) succeed (numbero x1)))

    (tassert "reduce pconstraint pconstraint" (simplify-pconstraint (numbero x1) (numbero x1)) (list succeed succeed succeed (numbero x1)))
    (tassert "reduce pconstraint pconstraint!" (simplify-pconstraint (symbolo x1) (numbero x1)) (list fail fail fail (numbero x1)))
    (tassert "reduce pconstraint ?pconstraint!" (simplify-pconstraint (symbolo x2) (numbero x1)) (list (numbero x1) (symbolo x2) succeed (numbero x1)))

    (tassert "reduce pconstraint =/= & pconstraint" (simplify-pconstraint (conj (=/= x1 1) (numbero x1)) (numbero x1)) (list succeed (=/= x1 1) succeed (numbero x1)))
    (tassert "reduce pconstraint pconstraint & =/=" (simplify-pconstraint (conj (numbero x1) (=/= x1 1)) (numbero x1)) (list succeed (=/= x1 1) succeed (numbero x1)))
    (tassert "reduce pconstraint == & ?==" (simplify-pconstraint (conj (== x1 1) (== x2 2)) (numbero x1)) (list succeed (conj (== x1 1) (== x2 2)) succeed (numbero x1)))

    (tassert "reduce pconstraint matcho" (simplify-pconstraint (matcho ([x1 (a . d)])) (numbero x1)) (list fail fail succeed (numbero x1)))

    
    (exit)

  
    
))
