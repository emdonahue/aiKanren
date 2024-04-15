(import (test-runner) (mk core) (mk core state) (mk core solver) (mk constraints) (mk core reducer) (mk core goals) (mk core matcho) (mk tracing))

(define x1 (var 1))
(define x2 (var 2))
(define x3 (var 3))
(define x4 (var 4))

(test-suite
 reducer

 ;; === EQUALITY ===
 (let* ([x1=1 (list (cons x1 1))]
        [x1=x2 (list (cons x1 x2))]
        [x1=x2x3 (list (cons x1 (cons x2 x3)))])
   ;; nothing=ground succeed, !=ground conflict, ?=free var, ^=bound var
   (tassert "reduce == & ==" (reduce-constraint2 (== x1 1) x1=1) succeed)
   (tassert "reduce == & ==!" (reduce-constraint2 (== x1 2) x1=1) fail)
   (tassert "reduce == & ==?" (reduce-constraint2 (== x1 x2) x1=1) (== x2 1))
   (tassert "reduce == & ?==" (reduce-constraint2 (== x2 2) x1=1) (== x2 2))
   (tassert "reduce == & ^==" (reduce-constraint2 (== x1 2) x1=x2) (== x2 2))
   (tassert "reduce == & ==*" (reduce-constraint2 (== x1 '(2 . 3)) x1=x2x3) (== (cons x2 x3) '(2 . 3)))
   (tassert "reduce == & ==!&==" (reduce-constraint2 (conj (== x1 2) (== x1 1)) x1=1) fail)
   (tassert "reduce == & ==&==!" (reduce-constraint2 (conj (== x1 1) (== x1 2)) x1=1) fail)

   (tassert "reduce == & =/=" (reduce-constraint2 (=/= x1 1) x1=1) fail)
   (tassert "reduce == & =/=!" (reduce-constraint2 (=/= x1 2) x1=1) succeed)
   (tassert "reduce == & =/=?" (reduce-constraint2 (=/= x1 1) x1=x2) (=/= x2 1))

   (tassert "reduce == & satisfied" (reduce-constraint2 (numbero x1) x1=1) succeed)
   (tassert "reduce == & not satisfied" (reduce-constraint2 (noto (numbero x1)) x1=1) fail)
   (tassert "reduce == & unsatisfiable" (reduce-constraint2 (symbolo x1) x1=1) fail)
   (tassert "reduce == & not unsatisfiable" (reduce-constraint2 (noto (symbolo x1)) x1=1) succeed)
   (tassert "reduce == & undecidable" (reduce-constraint2 (symbolo x2) x1=1) (symbolo x2))
   (tassert "reduce == & not undecidable" (reduce-constraint2 (noto (symbolo x2)) x1=1) (noto (symbolo x2)))
   (tassert "reduce ==f & undecidable" (reduce-constraint2 (symbolo x1) x1=x2) (symbolo x2))
   (tassert "reduce ==f & not undecidable" (reduce-constraint2 (noto (symbolo x1)) x1=x2) (noto (symbolo x2)))

   (tassert "reduce == & match fail" (reduce-constraint2 (matcho ([(a . d) x1])) x1=1) fail)
   (tassert "reduce == & match simplified" (reduce-constraint2 (matcho ([(a . d) x1])) x1=x2) (lambda (g) (and (matcho? g) (equal? (list x2) (matcho-attributed-vars g)))))
   (tassert "reduce == & match no vars succeed" (reduce-constraint2 (matcho ([(a . d) x1] [(b . c) x2])) `((,x1 . (1 . 2)) (,x2 . (3 . 4)))) succeed)
   (tassert "reduce == & match no vars fail" (reduce-constraint2 (matcho ([(a . d) x1] [(b . c) x2]) (== a 2)) `((,x1 . (1 . 2)) (,x2 . (3 . 4)))) fail)
   (tassert "reduce == & match unified out vars" (reduce-constraint2 (matcho ([(a . d) x1] [(b . c) x2])) x1=x2) (lambda (g) (and (matcho? g) (equal? (list x2) (matcho-attributed-vars g)))))
   (tassert "reduce == & match recheck unnormalized vars" (reduce-constraint2 (matcho ([(a . d) x1] [(b . c) x3])) x1=x2x3) (lambda (g) (and (matcho? g) (equal? (list x3) (matcho-attributed-vars g)))))
   (tassert "reduce == & match simplify normalized vars" (reduce-constraint2 (matcho ([(a . d) x1] [(b . c) x2])) (list (cons x1 '(1 . 2)) (cons x2 x3))) (lambda (g) (and (matcho? g) (equal? (matcho-attributed-vars g) (list x3)))))
   (tassert "reduce == & not match succeed" (reduce-constraint2 (noto (matcho ([(a . d) x1]))) x1=1) succeed)
   (tassert "reduce == & not match simplified" (reduce-constraint2 (noto (matcho ([(a . d) x1]))) x1=x2) (lambda (g) (and (noto? g) (matcho? (noto-goal g)) (equal? x2 (car (matcho-attributed-vars (noto-goal g)))))))
   (tassert "reduce == & not match recheck" (reduce-constraint2 (noto (matcho ([(a . d) x1] [(b . c) x2]))) x1=x2x3) (lambda (g) (and (noto? g) (matcho? (noto-goal g)) (equal? (matcho-attributed-vars (noto-goal g)) (list x2)))))

   (tassert "reduce == & ==!&==?" (reduce-constraint2 (disj (== x1 2) (== x2 3)) x1=1) (== x2 3))
   (tassert "reduce == & ==?&==?" (reduce-constraint2 (disj (== x2 2) (== x2 3)) x1=1) (disj (== x2 2) (== x2 3)))   
   (tassert "reduce == & match|unsatisfiable" (reduce-constraint2 (disj (matcho ([(a . d) x1]) (== a 1) (== d 2)) (=/= x1 (cons x2 x3))) x1=x2x3) (conj (== x2 1) (== x3 2)))
   (tassert "reduce == & =/=|unsatisfiable|undecidable" (reduce-constraint2 (disj (disj (=/= x2 2) (=/= x1 1)) (== x2 2)) x1=1) (disj (=/= x2 2) (== x2 2)))

   (tassert "reduce == & proxy succeed" (reduce-constraint2 (proxy x1) x1=1) succeed)
   (tassert "reduce == & proxy undecidable" (reduce-constraint2 (proxy x2) x1=1) (proxy x2)))

  ;; === DISEQUALITY ===
 (tassert "reduce =/= == succeed" (reduce-constraint2 (== x1 1) (=/= x1 1)) fail)
 (tassert "reduce =/= == undecidable" (reduce-constraint2 (== x1 (cons x2 x3)) (=/= x1 1)) (== x1 (cons x2 x3)))
 (tassert "reduce =/= =/= fail" (reduce-constraint2 (=/= x1 1) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= undecidable" (reduce-constraint2 (=/= x1 (cons x2 x3)) (=/= x1 1)) (=/= x1 (cons x2 x3)))
 (tassert "reduce =/= symbolo fail" (reduce-constraint2 (symbolo x1) (=/= x1 1)) (symbolo x1))
 (tassert "reduce =/= not numbero fail" (reduce-constraint2 (noto (numbero x1)) (=/= x1 1)) (noto (numbero x1)))
 (tassert "reduce =/= =/= succeed" (reduce-constraint2 (=/= x1 2) (=/= x1 1)) (=/= x1 2))
 (tassert "reduce =/= conj fail" (reduce-constraint2 (conj (== x1 1) (=/= x1 1)) (=/= x1 1)) fail)
 (tassert "reduce =/= match succeed" (reduce-constraint2 (matcho ([(a . d) x1])) (=/= x1 1)) matcho?)
 (tassert "reduce =/= not match succeed" (reduce-constraint2 (noto (matcho ([(a . d) x1])))  (=/= x1 1)) noto?)
 ;(tassert "reduce =/= proxy" (reduce-constraint2 (noto (matcho ([(a . d) x1])))  (=/= x1 1)) noto?)
 (tassert "reduce =/= =/= satisfied|satisfies" (reduce-constraint2 (disj (=/= x1 1) (symbolo x1)) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= satisfies|satisfies" (reduce-constraint2 (disj (symbolo x1) (symbolo x1)) (=/= x1 1)) (disj (symbolo x1) (symbolo x1)))
 (tassert "reduce =/= =/= satisfies|satisfied|unnormalized" (reduce-constraint2 (disj (=/= x1 1) (disj (symbolo x1) (=/= x2 2))) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= satisfied|satisfied|unnormalized" (reduce-constraint2 (disj (symbolo x1) (disj (symbolo x1) (=/= x2 2))) (=/= x1 1)) (disj (symbolo x1) (disj (symbolo x1) (=/= x2 2))))
 (tassert "reduce =/= =/= unsatisfiable|satisfied" (reduce-constraint2 (disj (== x1 1) (symbolo x1)) (=/= x1 1)) (symbolo x1))
 (tassert "reduce =/= =/= satisfied|unsatisfiable" (reduce-constraint2 (disj (symbolo x1) (== x1 1)) (=/= x1 1)) (symbolo x1))
 (tassert "reduce =/= =/= satisfied|unsatisfiable|undecidable" (reduce-constraint2 (disj (symbolo x1) (disj (== x1 1) (=/= x1 2))) (=/= x1 1)) (disj (symbolo x1) (=/= x1 2)))
 (tassert "reduce =/= =/= satisfied|undecidable" (reduce-constraint2 (disj (symbolo x1) (=/= x1 2)) (=/= x1 1)) (disj (symbolo x1) (=/= x1 2)))
 (tassert "reduce =/= =/= unsatisfiable|undecidable" (reduce-constraint2 (disj (== x1 1) (=/= x1 2)) (=/= x1 1)) (=/= x1 2))
 (tassert "reduce =/= =/= undecidable|unsatisfiable" (reduce-constraint2 (disj (=/= x1 2) (== x1 1)) (=/= x1 1)) (=/= x1 2))
 (tassert "reduce =/= =/= undecidable|undecidable" (reduce-constraint2 (disj (=/= x1 2) (=/= x1 3)) (=/= x1 1)) (disj (=/= x1 2) (=/= x1 3)))
 (tassert "reduce =/= =/= recheck|undecidable" (reduce-constraint2 (disj (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) (=/= x1 1)) (disj (conj (=/= x2 2) (=/= x2 3)) (=/= x1 3)))
 (tassert "reduce =/= =/= satisfied|recheck" (reduce-constraint2 (disj (symbolo x1) (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3)))) (=/= x1 1)) (disj (symbolo x1) (conj (=/= x2 2) (=/= x2 3))))
 (tassert "reduce =/= =/= satisfies|undecidable" (reduce-constraint2 (disj (=/= x1 1) (=/= x1 2)) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= undecidable|satisfies" (reduce-constraint2 (disj (=/= x1 2) (=/= x1 1)) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= =/=^|=/=^|=/=" (reduce-constraint2 (disj (=/= x1 2) (disj (=/= x1 3) (=/= x1 1))) (=/= x1 1)) succeed)
 (tassert "reduce =/= =/= ==^|==^|==" (reduce-constraint2 (disj (disj (== x1 2) (== x1 3)) (== x1 1)) (=/= x1 1)) (disj (== x1 2) (== x1 3)))
 (tassert "reduce =/= =/= ==^|==^|==|==^" (reduce-constraint2 (disj (disj (disj (== x1 2) (== x1 3)) (== x1 1)) (== x1 4)) (=/= x1 1)) (disj (disj (== x1 2) (== x1 3)) (== x1 4)))
 (tassert "reduce =/= =/= (recheck&recheck)|undecidable" (reduce-constraint2 (disj (conj (disj (== x1 1) (=/= x2 3)) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) (=/= x1 1)) (disj (conj (=/= x2 3) (=/= x2 3)) (=/= x1 3)))
 (tassert "reduce =/= =/= (satisfies|undecidable)|(satisfied|undecidable)" (reduce-constraint2 (disj (conj (=/= x1 2) (disj (=/= x1 1) (=/= x1 3))) (conj (=/= x1 4) (disj (symbolo x1) (=/= x1 5)))) (=/= x1 1)) (disj (=/= x1 2) (conj (=/= x1 4) (disj (symbolo x1) (=/= x1 5)))))
 (tassert "reduce =/= & proxy succeed" (reduce-constraint2 (proxy x1) (=/= x1 1)) succeed)
 (tassert "reduce =/= & proxy undecidable" (reduce-constraint2 (proxy x2) (=/= x1 1)) (proxy x2))

 ;; === CONJUNCTION ===
 (tassert "reduce conj =/= first simplifies" (reduce-constraint2 (=/= x1 1) (conj (=/= x1 1) (=/= x2 2))) succeed)
 (tassert "reduce conj =/= second simplifies" (reduce-constraint2 (=/= x1 1) (conj (=/= x2 2) (=/= x1 1))) succeed)
 (tassert "reduce conj =/= neither simplifies" (reduce-constraint2 (=/= x1 1) (conj (=/= x2 1) (=/= x2 2))) (=/= x1 1))
 (tassert "reduce conj =/= both simplify" (reduce-constraint2 (=/= x1 1) (conj (=/= x1 1) (=/= x1 1))) succeed)

 ;; === DISJUNCTION ===
 (tassert "reduce disj =/= first simplifies" (reduce-constraint2 (=/= x1 1) (disj (=/= x1 1) (=/= x2 2))) (=/= x1 1))
 (tassert "reduce disj =/= second simplifies" (reduce-constraint2 (=/= x1 1) (disj (=/= x2 2) (=/= x1 1))) (=/= x1 1))
 (tassert "reduce disj =/= neither simplifies" (reduce-constraint2 (=/= x1 1) (disj (=/= x2 1) (=/= x2 2))) (=/= x1 1))
 (tassert "reduce disj =/= both simplify" (reduce-constraint2 (=/= x1 1) (disj (=/= x1 1) (=/= x1 1))) succeed)

 ;; === PCONSTRAINT ===
 (tassert "reduce pconstraint ==" (reduce-constraint2 (== x1 1) (numbero x1)) (== x1 1))
 (tassert "reduce pconstraint ==!" (reduce-constraint2 (== x1 'symbol) (numbero x1)) fail)
 (tassert "reduce pconstraint ?==" (reduce-constraint2 (== x2 1) (numbero x1)) (== x2 1))
 (tassert "reduce pconstraint ?==!" (reduce-constraint2 (== x2 'symbol) (numbero x1)) (== x2 'symbol))
 (tassert "reduce pconstraint =/=" (reduce-constraint2 (=/= x1 1) (numbero x1)) (=/= x1 1))
 (tassert "reduce pconstraint =/=!" (reduce-constraint2 (=/= x1 'symbol) (numbero x1)) succeed)
 (tassert "reduce pconstraint ?==" (reduce-constraint2 (=/= x2 1) (numbero x1)) (=/= x2 1))
 (tassert "reduce pconstraint ?==!" (reduce-constraint2 (=/= x2 'symbol) (numbero x1)) (=/= x2 'symbol))

 #;
(begin
  (tassert "reduce pconstraint pconstraint" (reduce-constraint2 (numbero x1) (numbero x1)) (list succeed succeed succeed (numbero x1)))
  (tassert "reduce pconstraint noto pconstraint" (reduce-constraint2 (noto (numbero x1)) (numbero x1)) (list fail fail succeed (numbero x1)))
  (tassert "reduce pconstraint pconstraint!" (reduce-constraint2 (symbolo x1) (numbero x1)) (list fail fail succeed (numbero x1)))
  (tassert "reduce pconstraint noto pconstraint!" (reduce-constraint2 (noto (symbolo x1)) (numbero x1)) (list (numbero x1) succeed succeed (numbero x1)))
  (tassert "reduce pconstraint ?pconstraint!" (reduce-constraint2 (symbolo x2) (numbero x1)) (list (numbero x1) (symbolo x2) succeed (numbero x1)))
  (tassert "reduce pconstraint noto ?pconstraint!" (reduce-constraint2 (noto (symbolo x2)) (numbero x1)) (list (numbero x1) (noto (symbolo x2)) succeed (numbero x1)))

  (tassert "reduce pconstraint =/= & pconstraint" (reduce-constraint2 (conj (=/= x1 1) (numbero x1)) (numbero x1)) (list succeed (=/= x1 1) succeed (numbero x1)))
  (tassert "reduce pconstraint pconstraint & =/=" (reduce-constraint2 (conj (numbero x1) (=/= x1 1)) (numbero x1)) (list succeed (=/= x1 1) succeed (numbero x1)))
  (tassert "reduce pconstraint == & ?==" (reduce-constraint2 (conj (== x1 1) (== x2 2)) (numbero x1)) (list succeed (conj (== x1 1) (== x2 2)) succeed (numbero x1))))

 #;
 (begin
   (tassert "reduce pconstraint match!" (simplify-pconstraint (matcho ([x1 (a . d)])) (numbero x1)) (list fail fail succeed (numbero x1)))
   (tassert "reduce pconstraint match" (simplify-pconstraint (matcho ([x1 (a . d)])) (pairo x1)) (lambda (a) (and (succeed? (car a)) (matcho? (cadr a)))))
   (tassert "reduce pconstraint match?" (simplify-pconstraint (matcho ([x1 (a . d)])) (numbero x2)) (lambda (a) (and (equal? (car a) (numbero x2)) (matcho? (cadr a)))))
   (tassert "reduce pconstraint not match!" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (numbero x1)) (lambda (a) (and (equal? (car a) (numbero x1)) (succeed? (cadr a)))))
   (tassert "reduce pconstraint not match" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (pairo x1)) (lambda (a) (and (equal? (car a) (pairo x1)) (noto? (cadr a)))))
   (tassert "reduce pconstraint not match?" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (numbero x2)) (lambda (a) (and (equal? (car a) (numbero x2)) (noto? (cadr a))))))

 (tassert "reduce pconstraint satisfies|satisfied" (simplify-pconstraint (disj (numbero x1) (== x1 1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
 (tassert "reduce pconstraint satisfied|satisfies" (simplify-pconstraint (disj (== x1 1) (numbero x1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
 (tassert "reduce pconstraint unsatisfiable|satisfies" (simplify-pconstraint (disj (symbolo x1) (numbero x1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
 (tassert "reduce pconstraint unsatisfiable|undecidable" (simplify-pconstraint (disj (symbolo x1) (numbero x2)) (numbero x1)) (list (numbero x1) succeed (conj (numbero x1) (numbero x2)) succeed))
 (tassert "reduce pconstraint satisfied|undecidable" (simplify-pconstraint (disj (== x1 1) (numbero x2)) (numbero x1)) (list (numbero x1) (disj (== x1 1) (conj (numbero x1) (numbero x2))) succeed succeed))
 (tassert "reduce pconstraint undecidable|satisfied" (simplify-pconstraint (disj (numbero x2) (== x1 1)) (numbero x1)) (list (numbero x1) (disj (conj (numbero x1) (numbero x2)) (== x1 1)) succeed succeed))
 (tassert "reduce pconstraint undecidable|undecidable" (simplify-pconstraint (disj (numbero x2) (numbero x3)) (numbero x1)) (list (numbero x1) (conj (numbero x1) (disj (numbero x2) (numbero x3))) succeed succeed))
 (tassert "reduce pconstraint entails|entails" (simplify-pconstraint (disj (== x1 1) (== x1 2)) (numbero x1)) (list succeed (disj (== x1 1) (== x1 2)) succeed succeed))
 ;(tassert "reduce pconstraint simplifies|entailed" (simplify-pconstraint (disj (== x1 1) (matcho ([x1 (a d)]))) (pairo x1)) (lambda (g) (and (equal? (car g) (pairo x1)) (succeed? (cadr g)) (succeed? (cadddr g)) (matcho-test-eq? (caddr g) (list x1) '()))))

 ;;TODO test proxies
 
 )
