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
   (tassert "reduce == & ==" (reduce-constraint (== x1 1) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & ==!" (reduce-constraint (== x1 2) x1=1 #f) (list fail fail))
   (tassert "reduce == & ==?" (reduce-constraint (== x1 x2) x1=1 #f) (list (== x2 1) succeed))
   (tassert "reduce == & ?==" (reduce-constraint (== x2 2) x1=1 #f) (list (== x2 2) succeed))
   (tassert "reduce == & ^==" (reduce-constraint (== x1 2) x1=x2 #f) (list (== x2 2) succeed))
   (tassert "reduce == & ==*" (reduce-constraint (== x1 '(2 . 3)) x1=x2x3 #f) (list (== (cons x2 x3) '(2 . 3)) succeed))

   (tassert "reduce == & ==!&==" (reduce-constraint (conj (== x1 2) (== x1 1)) x1=1 #f) (list fail fail))
   (tassert "reduce == & ==&==!" (reduce-constraint (conj (== x1 1) (== x1 2)) x1=1 #f) (list fail fail))

   (tassert "reduce == & =/=" (reduce-constraint (=/= x1 1) x1=1 #f) (list fail fail))
   (tassert "reduce == & =/=!" (reduce-constraint (=/= x1 2) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & =/=?" (reduce-constraint (=/= x1 1) x1=x2 #f) (list (=/= x2 1) succeed))

   (tassert "reduce == & satisfied" (reduce-constraint (numbero x1) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & not satisfied" (reduce-constraint (noto (numbero x1)) x1=1 #f) (list fail fail))
   (tassert "reduce == & unsatisfiable" (reduce-constraint (symbolo x1) x1=1 #f) (list fail fail))
   (tassert "reduce == & not unsatisfiable" (reduce-constraint (noto (symbolo x1)) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & undecidable" (reduce-constraint (symbolo x2) x1=1 #f) (list (symbolo x2) succeed))
   (tassert "reduce == & not undecidable" (reduce-constraint (noto (symbolo x2)) x1=1 #f) (list (noto (symbolo x2)) succeed))
   (tassert "reduce ==f & undecidable" (reduce-constraint (symbolo x1) x1=x2 #f) (list (symbolo x2) succeed))
   (tassert "reduce ==f & not undecidable" (reduce-constraint (noto (symbolo x1)) x1=x2 #f) (list (noto (symbolo x2)) succeed))
   
   (tassert "reduce == & match fail" (reduce-constraint (matcho ([(a . d) x1])) x1=1 #f) (list fail fail))
   (tassert "reduce == & match simplified" (reduce-constraint (matcho ([(a . d) x1])) x1=x2 #f) (lambda (g) (and (matcho? (car g)) (equal? (list x2) (matcho-attributed-vars (car g))))))
   (tassert "reduce == & match no vars succeed" (reduce-constraint (matcho ([(a . d) x1] [(b . c) x2])) `((,x1 . (1 . 2)) (,x2 . (3 . 4))) #f) (list succeed succeed))
   (tassert "reduce == & match no vars fail" (reduce-constraint (matcho ([(a . d) x1] [(b . c) x2]) (== a 2)) `((,x1 . (1 . 2)) (,x2 . (3 . 4))) #f) (list fail fail))
   (tassert "reduce == & match unified out vars" (reduce-constraint (matcho ([(a . d) x1] [(b . c) x2])) x1=x2 #f) (lambda (g) (and (matcho? (car g)) (equal? (list x2) (matcho-attributed-vars (car g))))))
   (tassert "reduce == & match recheck unnormalized vars" (reduce-constraint (matcho ([(a . d) x1] [(b . c) x3])) x1=x2x3 #f) (lambda (g) (and (matcho? (car g)) (equal? (list x3) (matcho-attributed-vars (car g))))))
   (tassert "reduce == & match simplify normalized vars" (reduce-constraint (matcho ([(a . d) x1] [(b . c) x2])) (list (cons x1 '(1 . 2)) (cons x2 x3)) #f) (lambda (g) (and (matcho? (car g)) (equal? (matcho-attributed-vars (car g)) (list x3)))))
   (tassert "reduce == & not match succeed" (reduce-constraint (noto (matcho ([(a . d) x1]))) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & not match simplified" (reduce-constraint (noto (matcho ([(a . d) x1]))) x1=x2 #f) (lambda (g) (and (noto? (car g)) (matcho? (noto-goal (car g))) (equal? x2 (car (matcho-attributed-vars (noto-goal (car g))))))))
   (tassert "reduce == & not match recheck" (reduce-constraint (noto (matcho ([(a . d) x1] [(b . c) x2]))) x1=x2x3 #f) (lambda (g) (and (noto? (car g)) (matcho? (noto-goal (car g))) (equal? (matcho-attributed-vars (noto-goal (car g))) (list x2)))))

   (tassert "reduce == & ==!|==?" (reduce-constraint (disj (== x1 2) (== x2 3)) x1=1 #f) (list succeed (== x2 3)))
   (tassert "reduce == & ==?|==?" (reduce-constraint (disj (== x2 2) (== x2 3)) x1=1 #f) (list (disj (== x2 2) (== x2 3)) succeed))   
   (tassert "reduce == & match|unsatisfiable" (reduce-constraint (disj (matcho ([(a . d) x1]) (== a 1) (== d 2)) (=/= x1 (cons x2 x3))) x1=x2x3 #f) (list (conj (== x2 1) (== x3 2)) succeed))
   (tassert "reduce == & =/=|unsatisfiable|undecidable" (reduce-constraint (disj (disj (=/= x2 2) (=/= x1 1)) (== x2 2)) x1=1 #f) (list (disj (=/= x2 2) (== x2 2)) succeed))

   (tassert "reduce == & proxy succeed" (reduce-constraint (proxy x1) x1=1 #f) (list succeed succeed))
   (tassert "reduce == & proxy undecidable" (reduce-constraint (proxy x2) x1=1 #f) (list (proxy x2) succeed)))


  ;; === DISEQUALITY ===
 (tassert "reduce =/= == succeed" (reduce-constraint (== x1 1) (=/= x1 1) #f) (list fail fail))
 (tassert "reduce =/= == undecidable" (reduce-constraint (== x1 (cons x2 x3)) (=/= x1 1) #f) (list (== x1 (cons x2 x3)) succeed))
 (tassert "reduce =/= =/= fail" (reduce-constraint (=/= x1 1) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= undecidable" (reduce-constraint (=/= x1 (cons x2 x3)) (=/= x1 1) #f) (list (=/= x1 (cons x2 x3)) succeed))
 (tassert "reduce =/= symbolo fail" (reduce-constraint (symbolo x1) (=/= x1 1) #f) (list (symbolo x1) succeed))
 (tassert "reduce =/= not numbero fail" (reduce-constraint (noto (numbero x1)) (=/= x1 1) #f) (list (noto (numbero x1)) succeed))
 (tassert "reduce =/= =/= succeed" (reduce-constraint (=/= x1 2) (=/= x1 1) #f) (list (=/= x1 2) succeed))
 (tassert "reduce =/= conj fail" (reduce-constraint (conj (== x1 1) (=/= x1 1)) (=/= x1 1) #f) (list fail fail))
 (tassert "reduce =/= match succeed" (reduce-constraint (matcho ([(a . d) x1])) (=/= x1 1) #f) (lambda (g) (and (matcho? (car g)) (succeed? (cadr g)))))
 (tassert "reduce =/= not match succeed" (reduce-constraint (noto (matcho ([(a . d) x1])))  (=/= x1 1) #f) (lambda (g) (noto? (car g))))
 ;(tassert "reduce =/= proxy" (reduce-constraint (noto (matcho ([(a . d) x1])))  (=/= x1 1) #f) noto?)
 (tassert "reduce =/= =/= satisfied|satisfies" (reduce-constraint (disj (=/= x1 1) (symbolo x1)) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= satisfies|satisfies" (reduce-constraint (disj (symbolo x1) (symbolo x1)) (=/= x1 1) #f) (list (disj (symbolo x1) (symbolo x1)) succeed))
 (tassert "reduce =/= =/= satisfies|satisfied|unnormalized" (reduce-constraint (disj (=/= x1 1) (disj (symbolo x1) (=/= x2 2))) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= satisfied|satisfied|unnormalized" (reduce-constraint (disj (symbolo x1) (disj (symbolo x1) (=/= x2 2))) (=/= x1 1) #f) (list (disj (symbolo x1) (disj (symbolo x1) (=/= x2 2))) succeed))
 (tassert "reduce =/= =/= unsatisfiable|satisfied" (reduce-constraint (disj (== x1 1) (symbolo x1)) (=/= x1 1) #f) (list succeed (symbolo x1)))
 (tassert "reduce =/= =/= satisfied|unsatisfiable" (reduce-constraint (disj (symbolo x1) (== x1 1)) (=/= x1 1) #f) (list (symbolo x1) succeed))
 (tassert "reduce =/= =/= satisfied|unsatisfiable|undecidable" (reduce-constraint (disj (symbolo x1) (disj (== x1 1) (=/= x1 2))) (=/= x1 1) #f) (list (disj (symbolo x1) (=/= x1 2)) succeed))
 (tassert "reduce =/= =/= satisfied|undecidable" (reduce-constraint (disj (symbolo x1) (=/= x1 2)) (=/= x1 1) #f) (list (disj (symbolo x1) (=/= x1 2)) succeed))
 (tassert "reduce =/= =/= unsatisfiable|undecidable" (reduce-constraint (disj (== x1 1) (=/= x1 2)) (=/= x1 1) #f) (list succeed (=/= x1 2)))
 (tassert "reduce =/= =/= undecidable|unsatisfiable" (reduce-constraint (disj (=/= x1 2) (== x1 1)) (=/= x1 1) #f) (list (=/= x1 2) succeed))
 (tassert "reduce =/= =/= undecidable|undecidable" (reduce-constraint (disj (=/= x1 2) (=/= x1 3)) (=/= x1 1) #f) (list (disj (=/= x1 2) (=/= x1 3)) succeed))
 (tassert "reduce =/= =/= recheck|undecidable" (reduce-constraint (disj (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) (=/= x1 1) #f) (list succeed (disj (conj (=/= x2 2) (=/= x2 3)) (=/= x1 3))))
 (tassert "reduce =/= =/= satisfied|recheck" (reduce-constraint (disj (symbolo x1) (conj (=/= x2 2) (disj (== x1 1) (=/= x2 3)))) (=/= x1 1) #f) (list (disj (symbolo x1) (conj (=/= x2 2) (=/= x2 3))) succeed))
 (tassert "reduce =/= =/= satisfies|undecidable" (reduce-constraint (disj (=/= x1 1) (=/= x1 2)) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= undecidable|satisfies" (reduce-constraint (disj (=/= x1 2) (=/= x1 1)) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= =/=^|=/=^|=/=" (reduce-constraint (disj (=/= x1 2) (disj (=/= x1 3) (=/= x1 1))) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= =/= ==^|==^|==" (reduce-constraint (disj (disj (== x1 2) (== x1 3)) (== x1 1)) (=/= x1 1) #f) (list (disj (== x1 2) (== x1 3)) succeed))
 (tassert "reduce =/= =/= ==^|==^|==|==^" (reduce-constraint (disj (disj (disj (== x1 2) (== x1 3)) (== x1 1)) (== x1 4)) (=/= x1 1) #f) (list (disj (disj (== x1 2) (== x1 3)) (== x1 4)) succeed))
 (tassert "reduce =/= =/= (recheck&recheck)|undecidable" (reduce-constraint (disj (conj (disj (== x1 1) (=/= x2 3)) (disj (== x1 1) (=/= x2 3))) (=/= x1 3)) (=/= x1 1) #f) (list succeed (disj (conj (=/= x2 3) (=/= x2 3)) (=/= x1 3))))
 (tassert "reduce =/= =/= (satisfies|undecidable)|(satisfied|undecidable)" (reduce-constraint (disj (conj (=/= x1 2) (disj (=/= x1 1) (=/= x1 3))) (conj (=/= x1 4) (disj (symbolo x1) (=/= x1 5)))) (=/= x1 1) #f) (list (disj (=/= x1 2) (conj (=/= x1 4) (disj (symbolo x1) (=/= x1 5)))) succeed))
 (tassert "reduce =/= & proxy succeed" (reduce-constraint (proxy x1) (=/= x1 1) #f) (list succeed succeed))
 (tassert "reduce =/= & proxy undecidable" (reduce-constraint (proxy x2) (=/= x1 1) #f) (list succeed (proxy x2)))
 

 ;; === CONJUNCTION ===
 (tassert "reduce conj =/= first simplifies" (reduce-constraint (=/= x1 1) (conj (=/= x1 1) (=/= x2 2)) #f) (list succeed succeed))
 (tassert "reduce conj =/= second simplifies" (reduce-constraint (=/= x1 1) (conj (=/= x2 2) (=/= x1 1)) #f) (list succeed succeed))
 (tassert "reduce conj =/= neither simplifies" (reduce-constraint (=/= x1 1) (conj (=/= x2 1) (=/= x2 2)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce conj =/= both simplify" (reduce-constraint (=/= x1 1) (conj (=/= x1 1) (=/= x1 1)) #f) (list succeed succeed))

 ;; === DISJUNCTION ===
 (tassert "reduce disj =/= lhs succeeds" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (=/= x2 2)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce disj =/= rhs succeeds" (reduce-constraint (=/= x1 1) (disj (=/= x2 2) (=/= x1 1)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce disj =/= neither succeeds" (reduce-constraint (=/= x1 1) (disj (=/= x2 1) (=/= x2 2)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce disj =/= both succeed" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (=/= x1 1)) #f) (list succeed succeed))
 (tassert "reduce disj =/= lhs fails" (reduce-constraint (=/= x1 1) (disj (== x1 1) (=/= x2 2)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce disj =/= rhs fails" (reduce-constraint (=/= x1 1) (disj (=/= x2 2) (== x1 1)) #f) (list (=/= x1 1) succeed))
 (tassert "reduce disj =/= both fail" (reduce-constraint (=/= x1 1) (disj (== x1 1) (== x1 1)) #f) (list fail fail))
 (tassert "reduce disj =/= ==! =/=" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (== x1 1)) #f) (list succeed succeed))
 (tassert "reduce disj =/= =/= ==!" (reduce-constraint (=/= x1 1) (disj (== x1 1) (=/= x1 1)) #f) (list succeed succeed))
 (tassert "reduce disj =/= lhs reduces" (reduce-constraint (=/= x1 1) (disj (== x1 x2) (== x1 1)) #f) (list (=/= x2 1) succeed))
 (tassert "reduce disj =/= rhs reduces" (reduce-constraint (=/= x1 1) (disj (== x1 1) (== x1 x2)) #f) (list (=/= x2 1) succeed))
 ;(tassert "reduce disj =/= both reduce" (reduce-constraint (=/= x1 1) (disj (== x1 x2) (== x1 x2)) #f) (list (=/= x2 1) succeed))

 ;; === ASYMMETRIC ===
 (tassert "reduce asym =/= =/=|=/=" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (=/= x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==|=/=" (reduce-constraint (=/= x1 1) (disj (== x1 2) (=/= x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= =/=|==" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (== x1 2)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==!|=/=" (reduce-constraint (=/= x1 1) (disj (== x1 1) (=/= x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= =/=|==!" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (== x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==|==" (reduce-constraint (=/= x1 1) (disj (== x1 2) (== x1 2)) #t) (list succeed succeed))
 (tassert "reduce asym =/= ==!|=/=" (reduce-constraint (=/= x1 1) (disj (== x1 1) (=/= x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= =/=|==!" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (== x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==!|==" (reduce-constraint (=/= x1 1) (disj (== x1 1) (== x1 2)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==|==!" (reduce-constraint (=/= x1 1) (disj (=/= x1 1) (== x1 1)) #t) (list (=/= x1 1) succeed))
 (tassert "reduce asym =/= ==!|==!" (reduce-constraint (=/= x1 1) (disj (== x1 1) (== x1 1)) #t) (list fail fail))
 
 ;; === PCONSTRAINT ===
 (tassert "reduce pconstraint ==" (reduce-constraint (== x1 1) (numbero x1) #f) (list (== x1 1) succeed))
 (tassert "reduce pconstraint ==!" (reduce-constraint (== x1 'symbol) (numbero x1) #f) (list fail fail))
 (tassert "reduce pconstraint ?==" (reduce-constraint (== x2 1) (numbero x1) #f) (list (== x2 1) succeed))
 (tassert "reduce pconstraint ?==!" (reduce-constraint (== x2 'symbol) (numbero x1) #f) (list (== x2 'symbol) succeed))
 (tassert "reduce pconstraint =/=" (reduce-constraint (=/= x1 1) (numbero x1) #f) (list (=/= x1 1) succeed))
 (tassert "reduce pconstraint =/=!" (reduce-constraint (=/= x1 'symbol) (numbero x1) #f) (list succeed succeed))
 (tassert "reduce pconstraint ?==" (reduce-constraint (=/= x2 1) (numbero x1) #f) (list (=/= x2 1) succeed))
 (tassert "reduce pconstraint ?==!" (reduce-constraint (=/= x2 'symbol) (numbero x1) #f) (list (=/= x2 'symbol) succeed))

 ;; If the noto fails with the values, negate the success with the =/= if available
 (tassert "reduce !pconstraint ==!" (reduce-constraint (== x1 1) (noto (numbero x1)) #f) (list fail fail)) ; ==, succeed
 (tassert "reduce !pconstraint ==" (reduce-constraint (== x1 1) (noto (symbolo x1)) #f) (list (== x1 1) succeed)) ; fail, fail
 (tassert "reduce !pconstraint =/=!" (reduce-constraint (=/= x1 1) (noto (numbero x1)) #f) (list succeed succeed)) ; =/=, numbero
 (tassert "reduce !pconstraint =/=" (reduce-constraint (=/= x1 1) (noto (symbolo x1)) #f) (list (=/= x1 1) succeed)) ; succeed, symbolo
 (tassert "reduce !pconstraint ==!^" (reduce-constraint (== x2 1) (noto (numbero x1)) #f) (list (== x2 1) succeed))
 (tassert "reduce !pconstraint =/=!" (reduce-constraint (=/= x2 1) (noto (numbero x1)) #f) (list (=/= x2 1) succeed))


 #;
(begin
  (tassert "reduce pconstraint pconstraint" (reduce-constraint (numbero x1) (numbero x1) #f) (list succeed succeed succeed (numbero x1)))
  (tassert "reduce pconstraint noto pconstraint" (reduce-constraint (noto (numbero x1)) (numbero x1) #f) (list fail fail succeed (numbero x1)))
  (tassert "reduce pconstraint pconstraint!" (reduce-constraint (symbolo x1) (numbero x1) #f) (list fail fail succeed (numbero x1)))
  (tassert "reduce pconstraint noto pconstraint!" (reduce-constraint (noto (symbolo x1)) (numbero x1) #f) (list (numbero x1) succeed succeed (numbero x1)))
  (tassert "reduce pconstraint ?pconstraint!" (reduce-constraint (symbolo x2) (numbero x1) #f) (list (numbero x1) (symbolo x2) succeed (numbero x1)))
  (tassert "reduce pconstraint noto ?pconstraint!" (reduce-constraint (noto (symbolo x2)) (numbero x1) #f) (list (numbero x1) (noto (symbolo x2)) succeed (numbero x1)))

  (tassert "reduce pconstraint =/= & pconstraint" (reduce-constraint (conj (=/= x1 1) (numbero x1)) (numbero x1) #f) (list succeed (=/= x1 1) succeed (numbero x1)))
  (tassert "reduce pconstraint pconstraint & =/=" (reduce-constraint (conj (numbero x1) (=/= x1 1)) (numbero x1) #f) (list succeed (=/= x1 1) succeed (numbero x1)))
  (tassert "reduce pconstraint == & ?==" (reduce-constraint (conj (== x1 1) (== x2 2)) (numbero x1) #f) (list succeed (conj (== x1 1) (== x2 2)) succeed (numbero x1))))


 
(begin
  (tassert "reduce pconstraint satisfies|satisfied" (simplify-pconstraint (disj (numbero x1) (== x1 1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
  (tassert "reduce pconstraint satisfied|satisfies" (simplify-pconstraint (disj (== x1 1) (numbero x1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
  (tassert "reduce pconstraint unsatisfiable|satisfies" (simplify-pconstraint (disj (symbolo x1) (numbero x1)) (numbero x1)) (list succeed succeed succeed (numbero x1)))
  (tassert "reduce pconstraint unsatisfiable|undecidable" (simplify-pconstraint (disj (symbolo x1) (numbero x2)) (numbero x1)) (list (numbero x1) succeed (conj (numbero x1) (numbero x2)) succeed))
  (tassert "reduce pconstraint satisfied|undecidable" (simplify-pconstraint (disj (== x1 1) (numbero x2)) (numbero x1)) (list (numbero x1) (disj (== x1 1) (conj (numbero x1) (numbero x2))) succeed succeed))
  (tassert "reduce pconstraint undecidable|satisfied" (simplify-pconstraint (disj (numbero x2) (== x1 1)) (numbero x1)) (list (numbero x1) (disj (conj (numbero x1) (numbero x2)) (== x1 1)) succeed succeed))
  (tassert "reduce pconstraint undecidable|undecidable" (simplify-pconstraint (disj (numbero x2) (numbero x3)) (numbero x1)) (list (numbero x1) (conj (numbero x1) (disj (numbero x2) (numbero x3))) succeed succeed))
  (tassert "reduce pconstraint entails|entails" (simplify-pconstraint (disj (== x1 1) (== x1 2)) (numbero x1)) (list succeed (disj (== x1 1) (== x1 2)) succeed succeed))
)
 ;(tassert "reduce pconstraint simplifies|entailed" (simplify-pconstraint (disj (== x1 1) (matcho ([x1 (a d)]))) (pairo x1)) (lambda (g) (and (equal? (car g) (pairo x1)) (succeed? (cadr g)) (succeed? (cadddr g)) (matcho-test-eq? (caddr g) (list x1) '()))))

 ;;TODO test proxies

 ;; === MATCHO ===

 (tassert "reduce matcho ==" (reduce-constraint (== x1 (cons x2 x3)) (matcho ([(a . d) x1])) #f) (list (== x1 (cons x2 x3)) succeed))
 (tassert "reduce matcho ==!" (reduce-constraint (== x1 1) (matcho ([(a . d) x1])) #f) (list fail fail))
 (tassert "reduce matcho =/=" (reduce-constraint (=/= x1 (cons x2 x3)) (matcho ([(a . d) x1])) #f) (list (=/= x1 (cons x2 x3)) succeed))
 (tassert "reduce matcho =/=!" (reduce-constraint (=/= x1 1) (matcho ([(a . d) x1])) #f) (list succeed succeed))
  #;
 (begin
   (tassert "reduce pconstraint match!" (simplify-pconstraint (matcho ([x1 (a . d)])) (numbero x1)) (list fail fail succeed (numbero x1)))
   (tassert "reduce pconstraint match" (simplify-pconstraint (matcho ([x1 (a . d)])) (pairo x1)) (lambda (a) (and (succeed? (car a)) (matcho? (cadr a)))))
   (tassert "reduce pconstraint match?" (simplify-pconstraint (matcho ([x1 (a . d)])) (numbero x2)) (lambda (a) (and (equal? (car a) (numbero x2)) (matcho? (cadr a)))))
   (tassert "reduce pconstraint not match!" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (numbero x1)) (lambda (a) (and (equal? (car a) (numbero x1)) (succeed? (cadr a)))))
   (tassert "reduce pconstraint not match" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (pairo x1)) (lambda (a) (and (equal? (car a) (pairo x1)) (noto? (cadr a)))))
 (tassert "reduce pconstraint not match?" (simplify-pconstraint (noto (matcho ([x1 (a . d)]))) (numbero x2)) (lambda (a) (and (equal? (car a) (numbero x2)) (noto? (cadr a))))))

 ;; === PROXY ===
 (tassert "reduce proxy ==" (reduce-constraint (== x1 1) (proxy x1) #f) (list (== x1 1) succeed))
 (tassert "reduce proxy proxy" (reduce-constraint (proxy x1) (proxy x1) #f) (list succeed succeed))
 
 )
