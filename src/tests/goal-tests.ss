(import (test-runner) (mk) (utils) (goals) (streams) (variables))

(define x1 (make-var 1))
(define x2 (make-var 2))

(test-suite
 goals
 (tassert "goal == simplifies atoms fail" (== 1 2) fail)
 (tassert "goal == simplifies atoms succeed" (== 1 1) succeed)
 (tassert "goal =/= simplifies atoms fail" (=/= 1 2) succeed)
 (tassert "goal =/= simplifies atoms succeed" (=/= 1 1) fail)
 (tassert "goal conj simplifies succeed" (conj succeed succeed) succeed)
 (tassert "goal conj simplifies fail" (conj (== x1 1) fail) fail)
 (tassert "goal conde simplifies fail" (conde [(== x1 1)] [fail]) (== x1 1))

 (tassert "run unify free-ground" (run 1 q (== q 1)) '(1))
 (tassert "run unify free-ground take all" (run 2 q (== q 1)) '(1))
 (tassert "run conj no-ops" (run 1 q (== 2 2) (== q q) (== q 1) (== 2 2)) '(1))

 (tassert "run* unify free-ground" (run* q (== q 1)) '(1))
 (tassert "run* unify free-ground take all" (run* q (== q 1)) '(1))
 (tassert "run* conj no-ops" (run* q (== 2 2) (== q q) (== q 1) (== 2 2)) '(1))

 (tassert "run conj two bindings" (run 1 (q r) (== q 1) (== r 2)) '((1 2)))
 (tassert "run disj 2 empty states" (run -1 () (conde [(== 1 1)] [(== 2 2)])) '(() ()))
 (tassert "run disj 3 empty states" (run -1 () (conde [(== 1 1)] [(== 2 2)] [(== 3 3)])) '(() () ()))
 (tassert "run disj 3 unifications" (run -1 q (conde [(== q 1)] [(== q 2)] [(== q 3)])) '(1 2 3)) 
 (tassert "fresh" (run -1 q (fresh (x1) (== q x1) (== x1 1))) '(1))
 (tassert "empty fresh" (run -1 q (fresh () (== q 1))) '(1))

 (tassert "run* conj two bindings" (run* (q r) (== q 1) (== r 2)) '((1 2)))
 (tassert "run* disj 2 empty states" (run* () (conde [(== 1 1)] [(== 2 2)])) '(() ()))
 (tassert "run* disj 3 empty states" (run* () (conde [(== 1 1)] [(== 2 2)] [(== 3 3)])) '(() () ()))
 (tassert "run* disj 3 unifications" (run* q (conde [(== q 1)] [(== q 2)] [(== q 3)])) '(1 2 3)) 
 (tassert "run* fresh" (run* q (fresh (x1) (== q x1) (== x1 1))) '(1))

 (tassert "succeed goal" (run -1 x1 succeed) (list x1))
 (tassert "fail goal" (run -1 x1 fail) '())
 (tassert "conj fail" (run -1 x1 (conj* succeed fail)) '())
 (tassert "conj fail 2" (run -1 x1 (conj* fail succeed)) '())
 (tassert "bind" (run -1 x1 (fresh (x2) (fresh (x3) (fresh (x4) (== x1 1))))) '(1))

 (tassert "run* succeed goal" (run* x1 succeed) (list x1))
 (tassert "run* fail goal" (run* x1 fail) '())
 (tassert "run* conj fail" (run* x1 (conj* succeed fail)) '())
 (tassert "run* conj fail 2" (run* x1 (conj* fail succeed)) '())
 (tassert "run* bind" (run* x1 (fresh (x2) (fresh (x3) (fresh (x4) (== x1 1))))) '(1))

 (tassert "mplus fail lhs" (run -1 x1 (conde [fail] [(== x1 1)])) '(1))
 (tassert "mplus fail rhs" (run -1 x1 (conde [(== x1 1)] [fail])) '(1))
 (tassert "mplus answer lhs" (run -1 x1 (conde [(== x1 1)] [(== x1 2)])) '(1 2))
 (tassert "mplus answers lhs" (run -1 x1 (conde [(conde [(== x1 1)] [(== x1 3)])] [(== x1 2)])) '(1 2 3))    
 (tassert "mplus mplus" (run -1 x1 (conde [(conde [(fresh (x2) (== x1 1))] [(fresh (x2) (== x1 3))])]
                                          [(conde [(fresh (x2) (== x1 2))] [(fresh (x2) (== x1 4))])])) '(1 2 3 4))

 (tassert "run* mplus fail lhs" (run* x1 (conde [fail] [(== x1 1)])) '(1))
 (tassert "run* mplus fail rhs" (run* x1 (conde [(== x1 1)] [fail])) '(1))
 (tassert "run* mplus answer lhs" (run* x1 (conde [(== x1 1)] [(== x1 2)])) '(1 2))
 (tassert "run* mplus answers lhs" (run* x1 (conde [(conde [(== x1 1)] [(== x1 3)])] [(== x1 2)])) '(1 3 2))    
 (tassert "run* mplus mplus" (run* x1 (conde [(conde [(fresh (x2) (== x1 1))] [(fresh (x2) (== x1 3))])]
                                             [(conde [(fresh (x2) (== x1 2))] [(fresh (x2) (== x1 4))])])) '(1 3 2 4))

 ;; TODO determine whether bind should halt after every fresh or only those that generate mplus/binds
 (tassert "mplus answer rhs" (run -1 x1 (conde [(fresh (x2) (== x1 2))] [(== x1 1)])) '(1 2))
 (tassert "mplus answers rhs" (run -1 x1 (conde [(fresh (x2) (== x1 3))] [(conde [(== x1 1)] [(== x1 2)])])) '(1 2 3))
 (tassert "mplus bind" (run -1 x1 (conde [(fresh (x2) (fresh (x3) (== x1 2)))] [(fresh (x2) (== x1 1))])) '(1 2))

 (tassert "run* mplus answer rhs" (run* x1 (conde [(fresh (x2) (== x1 2))] [(== x1 1)])) '(2 1))
 (tassert "run* mplus answers rhs" (run* x1 (conde [(fresh (x2) (== x1 3))] [(conde [(== x1 1)] [(== x1 2)])])) '(3 1 2))
 (tassert "run* mplus bind" (run* x1 (conde [(fresh (x2) (fresh (x3) (== x1 2)))] [(fresh (x2) (== x1 1))])) '(2 1))

 (tassert "bind failure" (run -1 x1 fail (fresh (x2) (== 1 x1))) '())
 (tassert "bind answer" (run -1 (x1 x2) (== x1 1) (== x2 2)) '((1 2)))    
 (tassert "bind bind" (run -1 x1 (fresh (x2) (== x2 x1) (fresh (x3) (== x3 x2) (== x3 1)))) '(1))

 (tassert "bind answers" (run -1 (x1 x2) (== x2 3) (conde [(== x1 1)] [(== x1 2)])) '((1 3) (2 3)))
 (tassert "bind mplus" (run -1 (x1 x2) (== x2 3) (conde [(fresh (x3) (== x1 1))] [(fresh (x3) (== x1 2))])) '((1 3) (2 3)))

 (tassert "run* bind failure" (run* x1 fail (fresh (x2) (== 1 x1))) '())
 (tassert "run* bind answer" (run* (x1 x2) (== x1 1) (== x2 2)) '((1 2)))    
 (tassert "run* bind bind" (run* x1 (fresh (x2) (== x2 x1) (fresh (x3) (== x3 x2) (== x3 1)))) '(1))
 (tassert "run* bind answers" (run* (x1 x2) (== x2 3) (conde [(== x1 1)] [(== x1 2)])) '((1 3) (2 3)))
 (tassert "run* bind mplus" (run* (x1 x2) (== x2 3) (conde [(fresh (x3) (== x1 1))] [(fresh (x3) (== x1 2))])) '((1 3) (2 3)))

 (tassert "exist no vars" (run1 x1 (exist () (== x1 1))) 1)
 (tassert "exist var" (run1 x1 (exist (x2) (== x1 x2))) x2)

 (tassert "run* exist no vars" (run* x1 (exist () (== x1 1))) '(1))
 (tassert "run* exist var" (run* x1 (exist (x2) (== x1 x2))) (list x2))

 (tassert "occurs check simple lhs" (run1 x1 (== x1 (cons x1 2))) (void))
 (tassert "occurs check simple rhs" (run1 x1 (== x1 (cons 1 x1))) (void))
 (tassert "occurs check deep lhs" (run1 (x1 x2) (== x2 (list x1)) (== x1 (cons x2 2))) (void))
 (tassert "occurs check deep rhs" (run1 (x1 x2) (== x2 (list x1)) (== x1 (cons 1 x2))) (void))

 (tassert "run* occurs check simple lhs" (run* x1 (== x1 (cons x1 2))) '())
 (tassert "run* occurs check simple rhs" (run* x1 (== x1 (cons 1 x1))) '())
 (tassert "run* occurs check deep lhs" (run* (x1 x2) (== x2 (list x1)) (== x1 (cons x2 2))) '())
 (tassert "run* occurs check deep rhs" (run* (x1 x2) (== x2 (list x1)) (== x1 (cons 1 x2))) '())
 ;;(tassert "reify cyclic" (run1 x1 (== x1 (cons x1 x1))) (cons x1 x1)) ;TODO test reify cyclic once unsound unification implemented

 (parameterize ([answer-type answer-type/state])
   (tassert "trivial fresh does not extend substitution" (state-varid (run1 x1 (fresh (x2) succeed))) 1)))
