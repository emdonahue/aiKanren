(import (chezscheme) (test-runner) (mk) (goals) (variables) (matcho) (utils))

(define x0 (make-var 0))
(define x1 (make-var 1))
(define x2 (make-var 2))
(define x3 (make-var 3))

(test-suite
 matcho



 (begin
   ;; Basic pattern tests

  (begin
    (tassert "match no patterns" (matcho11 () succeed) succeed)
    (tassert "match empty list" (matcho11 ([() '()]) succeed) succeed)
    (tassert "match number" (matcho11 ([1 1]) succeed) succeed)
    (tassert "match empty body" (matcho11 ([1 1])) succeed)
    (tassert "match simple variable rename" (matcho11 ([a 1]) (== x1 a)) (== x1 1))
    (tassert "match multiple empty list" (matcho11 ([() '()] [() '()]) succeed) succeed)
    (tassert "match prim-pair fail" (run1 x1 (matcho11 ([(a 2) 1]) (== a x1))) (void))
    (tassert "match prim-null fail" (run1 x1 (matcho11 ([(a 2) '()]) (== a x1))) (void))
    (tassert "match ground pair" (matcho11 ([(a . d) '(1 . 2)]) (== x1 (cons d a))) (== x1 '(2 . 1)))
    (tassert "match non-pair fail" (matcho11 ([(a . d) 1]) succeed) fail)
    (tassert "match ground car fail" (matcho11 ([(2 . d) '(1 . 2)]) succeed) fail)
    (tassert "match ground cdr fail" (matcho11 ([(a . 1) '(1 . 2)]) succeed) fail)
    (tassert "match ground car succeed" (matcho11 ([(1 . d) '(1 . 2)]) (== x1 d)) (== x1 2))
    (tassert "match ground cdr succeed" (matcho11 ([(a . 2) '(1 . 2)]) (== x1 a)) (== x1 1))
    (tassert "match ground symbol car fail" (matcho11 ([('two . d) '(one . two)]) (== x1 d)) fail)
    (tassert "match ground symbol car succeed" (matcho11 ([('one . d) '(one . two)]) (== x1 d)) (== x1 'two))
    (tassert "match nested car" (matcho11 ([((a . b) . d) '((1 . 3) . 2)]) (== x1 (list a d b))) (== x1 '(1 2 3)))
    (tassert "match nested list" (matcho11 ([((a . b)) '((1 . 2))]) (== x1 (cons b a))) (== x1 '(2 . 1)))
    (tassert "match nested list var" (matcho11 ([((a . b)) '((1 . 2))]) (== x1 (cons b a))) (== x1 '(2 . 1))) 
    (tassert "match shared varname" (matcho11 ([a 1] [2 a]) succeed) fail)    
    (tassert "match list fail" (run1 () (matcho11 ([(a 1) '(1 2)]))) (void))
    (tassert "match list succeed" (run1 () (matcho11 ([(a 1) '(1 1)]))) '())
    (tassert "match list extract" (run1 (x1 x2) (matcho11 ([(a b) '(1 2)]) (== x1 a) (== x2 b))) '(1 2))
    (tassert "match list extend" (run1 x1 (matcho11 ([(a 2) (list 1 x1)]))) 2)
    (tassert "match pair fail" (run1 () (matcho11 ([(a . 1) '(1 . 2)]))) (void))
    (tassert "match pair succeed" (run1 () (matcho11 ([(a . 1) '(1 . 1)]))) '())
    (tassert "match pair extract" (run1 (x1 x2) (matcho11 ([(a . b) '(1 . 2)]) (== x1 a) (== x2 b))) '(1 2))
    (tassert "match pair extend" (run1 x1 (matcho11 ([(a . 2) (cons 1 x1)]))) 2)
    (tassert "match pair symbol" (run1 (x1 x2) (matcho11 ([(a . 'two) (cons 'one x2)]) (== a x1))) '(one two))
    (tassert "match pair symbol list" (run1 (x1 x2) (matcho11 ([(a . '(two three)) (cons 'one x2)]) (== a x1)))
             '(one (two three)))
    (tassert "match duplicate vars" (run1 x1 (matcho11 ([(a 2) '(1 2)] [(a 2) (list x1 2)]))) 1)    
    (tassert "match full ground pattern" (matcho11 ([(1 . 2) x1]) succeed) (== x1 '(1 . 2)))
    (tassert "match pattern ids bound" (matcho11 ([(a . d) '(1 . 2)] [(d . a) x1]) succeed) (== x1 '(2 . 1)))
    (tassert "match pattern ids bound reverse" (matcho11 ([(d . a) x1] [(a . d) '(1 . 2)]) succeed) (== x1 '(2 . 1)))
    (tassert "match in-var binds early" (matcho11 ([(a . d) '(1 . 2)] [(a . d) x1]) succeed) (== x1 '(1 . 2)))
    (tassert "match in-var binds late" (matcho11 ([(a . d) x1] [(a . d) '(1 . 2)]) succeed) (== x1 '(1 . 2)))
    (tassert "match in-var binds out-var" (matcho11 ([(a . d) (cons x1 x2)] [(a . d) '(1 . 2)]) succeed) (conj (== x1 1) (== x2 2)))
    (tassert "match duplicate patterns" (matcho11 ([(a . a) (cons x1 x2)])) (== x1 x2))
    (tassert "match pattern vars shadow bindings" (matcho11 ([(x2 . x1) (cons x1 x2)]) (== x2 2) (== x1 1)) (conj (== x1 2) (== x2 1)))
    )



  #;
  (pretty-print (expand '(matcho3 ([x2
                        ('closure ('lambda params body) env^)]) (== x1 (list params body env^)))))

    ;; Constraint matcho
    

  (begin
    (tassert "match constraint free" (matcho14-substitution (run1 x1 (constraint (matcho11 ([(a 2) x1]))))) (list (cons x1 (list x0 2))))
    (tassert "match constraint moves to free"
             (matcho14-substitution
              (run1 x1 (exist (x2) (constraint (matcho11 ([(a 2) x1]))) (== x1 x2)))) (list (cons x2 (list x0 2))))
    (tassert "match lazy constraint primitive fail" (run1 x1 (constraint (matcho11 ([(a . d) x1]) succeed)) (== x1 1)) (void))
    (tassert "match lazy constraint null fail" (run1 x1 (constraint (matcho11 ([(a . d) x1]) succeed)) (== x1 '())) (void))
    (tassert "match constraint unifies ground"
             (run1 (x1 x2 x3) (== x2 (list x3)) (constraint (matcho11 ([(a 2) x1] [(3) x2]))))
             (lambda (a) (and (matcho14? (car a)) (equal? (cadr a) '(3)) (equal? (caddr a) 3))))
    (tassert "match constraint runs immediately when bound"
             (run1 (x1 x2) (== x1 (cons x2 2)) (constraint (matcho11 ([(a . d) x1]) (== a 1)))) '((1 . 2) 1))
    (tassert "match constraint makes all unifications when fully ground"
             (run1 (x1 x2) (== x1 '(1 . 2)) (constraint (matcho11 ([(a . d) x1] [(a . d) x2])))) '((1 . 2) (1 . 2)))
    (tassert "match constraint disj first" (run1 (x1 x2) (constraint (matcho11 ([(a 2) x1] [(a 2) x2]) (== a 1))) (== x1 '(1 2))) '((1 2) (1 2)))
    (tassert "match constraint disj rest" (run1 (x1 x2) (constraint (matcho11 ([(a 2) x1] [(a 2) x2]) (== a 1))) (== x2 '(1 2))) '((1 2) (1 2)))
    (tassert "match constraint disj all" (run1 (x1 x2) (constraint (matcho11 ([(a 2) x1] [(a 2) x2]) (== a 1))) (== x1 '(1 2)) (== x2 x1)) '((1 2) (1 2)))
    (tassert "match constraint no fresh" (run1 (x1 x2) (constraint (matcho11 ([(a b) x1]))) (== x1 (list x2 x2))) (list (list x2 x2) x2))
    (tassert "match constraint simplifies ground" (run1 (x1 x2) (constraint (matcho11 ([(a . d) x1] [(b . c) x2]) (== (list a d b c) '(1 2 3 4)))) (== x1 '(1 . 2)) (== x2 '(3 . 4))) '((1 . 2) (3 . 4)))
    (tassert "match constraint simplifies var" (run1 (x1 x2) (constraint (matcho11 ([(a . d) x1] [(b . c) x2]) (== a 1))) (== x1 x2) (== x2 '(1 . 2))) '((1 . 2) (1 . 2)))
    (tassert "match constraint rechecks var" (run1 (x1 x2 x3) (== x3 x2) (constraint (matcho11 ([(a . d) x1] [(b . c) x3]) (== a 1))) (== x1 '(1 . 2))) (lambda (g) (and (equal? (car g) '(1 . 2)) (equal? (cadr g) (caddr g)) (matcho14? (conj-rhs (cadr g))) (proxy? (conj-lhs (cadr g))) (equal? (matcho-attributed-vars (conj-rhs (cadr g))) (list x3))))))

  ;; Negated matcho
  

  (begin 
    (tassert "match noto pattern fail" (run1 x1 (== x1 `(1 . 2)) (noto (matcho11 ([(2 . y) x1]) succeed))) '(1 . 2))
    (tassert "match noto pattern succeed" (run1 x1 (== x1 `(1 . 2)) (noto (matcho11 ([(1 . y) x1]) succeed))) (void))
    (tassert "match noto pattern disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho11 ([(1 . y) x1]) succeed))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto contents disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho11 ([(y . 2) x1]) (== 1 y)))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto optimized pair disequality" (run1 (x1 x2 x3) (== x1 `(,x2 . ,x3)) (noto (matcho11 ([(y . z) x1]) (conde [(== y 1)] [(== z 2)])))) (list (cons (=/= x2 1) (=/= x3 2)) (=/= x2 1) (=/= x3 2)))
    (tassert "noto expands match before negating" (run1 (x1 x2 x3) (== x3 3) (== x1 '(1 . 2)) (noto (matcho11 ([(a . d) x1]) (disj (=/= x2 a) (== x3 d))))) (list '(1 . 2) 1 3)))

  ;; Goal matcho
  

  (begin
    (tassert "match goal walk var" (run1 (x1 x2) (== x1 (cons 1 x2)) (matcho11 ([(a . d) x1]) (== a 1) (== d 2))) '((1 . 2) 2))
    (tassert "match create fresh" (run1 x1 (matcho11 ([(a . d) x1]) (== a 1) (== d 2))) '(1 . 2))
    (tassert "match goal fail" (run1 x1 (matcho11 ([(a . d) x1]) fail)) (void))
    (tassert "match expander differentiates between parent and child matcho"
             (run1 x1 (== x1 '(1 . 2)) (matcho11 ([(a . d) x1]) (matcho11 ([(a . d) x1]) (== a 1) (== d 2)))) '(1 . 2)))

  ;; Internal utilities
  
  
  (begin
    (tassert "terms build from patterns"
             (let ([a x1]) (pattern->term (1 () 'one (a)))) (list 1 '() 'one (list x1))))))
