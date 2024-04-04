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
    (tassert "match simple variable rename" (matcho11 ([a 1]) (== x1 a)) (== x1 1))
    (tassert "match multiple empty list" (matcho11 ([() '()] [() '()]) succeed) succeed)
    (tassert "match prim-pair fail" (run1 x1 (matcho11 ([(a 2) 1]) (== a x1))) (void))
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

    #;
    (tassert "expands match with nested proper lists"
             (matcho3 (['(closure (lambda 1 2) 3)
                        ('closure ('lambda params body) env^)]) (== x1 (list params body env^))) (== x1 '(1 2 3)))
    #;
    (tassert "suspends match with nested proper lists"
             (matcho3 ([x2
                        ('closure ('lambda params body) env^)]) (== x1 (list params body env^))) (== x1 '(1 2 3))))

  #;
  (pretty-print (expand '(matcho3 ([x2
                        ('closure ('lambda params body) env^)]) (== x1 (list params body env^)))))

  ;; Constraint matcho

  (begin
    (tassert "match constraint free" (matcho14-substitution (run1 x1 (constraint (matcho11 ([(a 2) x1]) (== a 1))))) (list (cons x1 (cons x0 2))))
    (tassert "match constraint disj first" (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2))) '((1 2) (1 2)))
    (tassert "match constraint disj rest" (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x2 '(1 2))) '((1 2) (1 2)))
    (tassert "match constraint disj all" (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2)) (== x2 x1)) '((1 2) (1 2)))
    (tassert "match constraint no fresh" (run1 (x1 x2) (constraint (matcho3 ([x1 (a b)]))) (== x1 (list x2 x2))) (list (list x2 x2) x2))
    (tassert "match constraint simplifies ground" (run1 (x1 x2) (constraint (matcho3 ([x1 (a . d)] [x2 (b . c)]) (== (list a d b c) '(1 2 3 4)))) (== x1 '(1 . 2)) (== x2 '(3 . 4))) '((1 . 2) (3 . 4)))
    (tassert "match constraint simplifies var" (run1 (x1 x2) (constraint (matcho3 ([x1 (a . d)] [x2 (b . c)]) (== a 1))) (== x1 x2) (== x2 '(1 . 2))) '((1 . 2) (1 . 2)))
    (tassert "match constraint rechecks var" (run1 (x1 x2 x3) (== x3 x2) (constraint (matcho3 ([x1 (a . d)] [x3 (b . c)]) (== a 1))) (== x1 '(1 . 2))) (lambda (g) (and (equal? (car g) '(1 . 2)) (equal? (cadr g) (caddr g)) (matcho4? (conj-rhs (cadr g))) (proxy? (conj-lhs (cadr g))) (equal? (matcho4-vars (conj-rhs (cadr g))) (list x3))))))

  ;; Negated matcho

  (begin 
    (tassert "match noto pattern fail" (run1 x1 (== x1 `(1 . 2)) (noto (matcho3 ([x1 (2 . y)]) succeed))) '(1 . 2))
    (tassert "match noto pattern succeed" (run1 x1 (== x1 `(1 . 2)) (noto (matcho3 ([x1 (1 . y)]) succeed))) (void))
    (tassert "match noto pattern disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho3 ([x1 (1 . y)]) succeed))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto contents disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho3 ([x1 (y . 2)]) (== 1 y)))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
    (tassert "match noto optimized pair disequality" (run1 (x1 x2 x3) (== x1 `(,x2 . ,x3)) (noto (matcho3 ([x1 (y . z)]) (conde [(== y 1)] [(== z 2)])))) (list (cons (=/= x2 1) (=/= x3 2)) (=/= x2 1) (=/= x3 2)))
    (tassert "noto expands match before negating" (run1 (x1 x2 x3) (== x3 3) (== x1 '(1 . 2)) (noto (matcho3 ([x1 (a . d)]) (disj (=/= x2 a) (== x3 d))))) (list '(1 . 2) 1 3)))

  ;; Suspended constraints
  
  (begin
    (tassert "match lazy constraint primitive fail" (run1 x1 (constraint (matcho3 ([x1 (a . d)]) succeed)) (== x1 1)) (void)))

  ;; Goal matcho

  (begin
    #;
    (begin 
      (tassert "match free" (matcho4-vars (matcho11 ([(a . d) x1]) (cons d a))) (list x1))
      (tassert "match free expand" ((matcho4-procedure (matcho11 ([(a . d) x1]) (== x2 (cons d a)))) '(1 . 2))
               (list #t succeed (== x2 '(2 . 1))))
      (tassert "match free expand quote" ((matcho4-procedure (matcho11 ([('one . d) x1]) (== x2 d))) '(one . 2))
               (list #t succeed (== x2 2)))
(tassert "match expander differentiates between parent and child matcho"
             (run1 x1 (== x1 '(1 . 2)) (matcho11 ([(a . d) x1]) (matcho11 ([(a . d) x1]) (== a 1) (== d 2)))) '(1 . 2)))
    (tassert "match goal walk var" (run1 x1 (== x1 '(1 . 2)) (matcho3 ([x1 (a . d)]) (== a 1) (== d 2))) '(1 . 2))
    (tassert "create fresh vars, ignore ground"
             (let ([vid 0]
                   [a 1])
               (matcho/fresh vid (a) ((a b () c) (b . 2) (1 . c) ((() d))) (list a b c d))) (list 1 x1 x2 x3))
    (tassert "terms build from patterns"
             (let ([a x1]) (pattern->term (1 () 'one (a)))) (list 1 '() 'one (list x1)))
    (tassert "build patterns in fresh"
             (let ([vid 0])
               (matcho/fresh vid () ((a . d)) (pattern->term ((a . d))))) (list (cons x1 x2)))
    (tassert "match create fresh" (run1 x1 (matcho3 ([x1 (a . d)]) (== a 1) (== d 2))) '(1 . 2))
    (tassert "match eager" (run* x1 (conde [(matcho3 ([(list 1 2) (a 2)]) (== a x1))] [(== x1 2)])) '(1 2))
    (tassert "match eager var" (run* x1 (conde [(matcho3 ([(list x1 2) (a 2)]) (== a 1))] [(== x1 2)])) '(1 2))
    (tassert "match eager bound var" (run* x1 (conde [(== x1 '(1 2)) (matcho3 ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2))
    (tassert "match eager bound vars" (run* (x1 x2) (conde [(== x2 '(1 2)) (matcho3 ([x1 (a 2)] [x2 (1 2)]) (== a 1))] [(== x1 3) (== x2 4)])) '(((1 2) (1 2)) (3 4)))
    (tassert "match lazy var" (run* x1 (conde [(matcho3 ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2)))
))
