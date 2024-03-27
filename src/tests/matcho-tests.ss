(import (chezscheme) (test-runner) (mk) (goals) (variables) (matcho) (utils))

(define x1 (make-var 1))
(define x2 (make-var 2))
(define x3 (make-var 3))

(test-suite
 matcho

 ;; Eager pattern matching

 (begin
   (tassert "match list fail" (run1 () (let ([m '(1 2)]) (matcho3 ([m (a 1)])))) (void))
   (tassert "match list succeed" (run1 () (let ([m '(1 1)]) (matcho3 ([m (a 1)])))) '())
   (tassert "match list extract" (run1 (x1 x2) (let ([m '(1 2)]) (matcho3 ([m (a b)]) (== x1 a) (== x2 b)))) '(1 2))
   (tassert "match list extend" (run1 x1 (let ([m (list 1 x1)]) (matcho3 ([m (a 2)])))) 2)
   (tassert "match pair fail" (run1 () (let ([m '(1 . 2)]) (matcho3 ([m (a . 1)])))) (void))
   (tassert "match pair succeed" (run1 () (let ([m '(1 . 1)]) (matcho3 ([m (a . 1)])))) '())
   (tassert "match pair extract" (run1 (x1 x2) (let ([m '(1 . 2)]) (matcho3 ([m (a . b)]) (== x1 a) (== x2 b)))) '(1 2))
   (tassert "match pair extend" (run1 x1 (let ([m (cons 1 x1)]) (matcho3 ([m (a . 2)])))) 2)
   (tassert "match pair symbol" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho3 ([m (a . 'two)]) (== a x1)))) '(one two))
   (tassert "match pair symbol list" (run1 (x1 x2) (let ([m (cons 'one x2)]) (matcho3 ([m (a . '(two three))]) (== a x1)))) '(one (two three)))
 (tassert "match duplicate vars" (run1 x1 (let ([m '(1 2)] [n (list x1 2)]) (matcho3 ([m (a 2)] [n (a 2)])))) 1)
 
   )

 ;; Fresh var instantiation
 ;(tassert "match optimized pair unifies cons" (run1 x1 (matcho3 ([x1 (a . d)]) (== a 1) (== d 2))) '(1 . 2))
 

 ;; Eagerly run matcho until we exhaust ground information
 (begin 
   (tassert "match eager" (run* x1 (conde [(let ([m (list 1 2)]) (matcho ([m (a 2)]) (== a x1)))] [(== x1 2)])) '(1 2))
   (tassert "match eager var" (run* x1 (conde [(let ([m (list x1 2)]) (matcho ([m (a 2)]) (== a 1)))] [(== x1 2)])) '(1 2))
   (tassert "match eager bound var" (run* x1 (conde [(== x1 '(1 2)) (matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2))
 (tassert "match eager bound vars" (run* (x1 x2) (conde [(== x2 '(1 2)) (matcho ([x1 (a 2)] [x2 (1 2)]) (== a 1))] [(== x1 3) (== x2 4)])) '(((1 2) (1 2)) (3 4)))
 (tassert "match lazy var" (run* x1 (conde [(matcho ([x1 (a 2)]) (== a 1))] [(== x1 2)])) '((1 2) 2)))

 ;; Constraint matcho
 (tassert "match constraint ground" (run1 x1 (let ([m '(1 2)]) (constraint (matcho3 ([m (a 2)]) (== a x1))))) 1)
 (tassert "match constraint ground-free" (run1 x1 (let ([m (list x1 2)]) (constraint (matcho3 ([m (a 2)]) (== a 1))))) 1)
 (tassert "match constraint free" (matcho4-vars (run1 x1 (constraint (matcho3 ([x1 (a 2)]) (== a 1))))) (list x1))
 (tassert "match constraint disj first" (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2))) (lambda (g) (and (equal? '(1 2) (car g)) (conj? (cadr g)) (proxy? (conj-lhs (cadr g))) (matcho4? (conj-rhs (cadr g))) (equal? (matcho4-vars (conj-rhs (cadr g))) (list x2)))))
 (tassert "match constraint disj rest" (matcho4-vars (car (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x2 '(1 2))))) (list x1))
 (tassert "match constraint disj all" (run1 (x1 x2) (constraint (matcho3 ([x1 (a 2)] [x2 (a 2)]) (== a 1))) (== x1 '(1 2)) (== x2 x1)) '((1 2) (1 2)))
 (tassert "match constraint no fresh" (run1 (x1 x2) (constraint (matcho3 ([x1 (a b)]))) (== x1 (list x2 x2))) (list (list x2 x2) x2))
 (tassert "match constraint simplifies ground" (run1 (x1 x2) (constraint (matcho3 ([x1 (a . d)] [x2 (b . c)]) (== (list a d b c) '(1 2 3 4)))) (== x1 '(1 . 2)) (== x2 '(3 . 4))) '((1 . 2) (3 . 4)))
 (tassert "match constraint simplifies var" (run1 (x1 x2) (constraint (matcho3 ([x1 (a . d)] [x2 (b . c)]) (== a 1))) (== x1 x2) (== x2 '(1 . 2))) '((1 . 2) (1 . 2)))
 (tassert "match constraint rechecks var" (run1 (x1 x2 x3) (== x3 x2) (constraint (matcho3 ([x1 (a . d)] [x3 (b . c)]) (== a 1))) (== x1 '(1 . 2))) (lambda (g) (and (equal? (car g) '(1 . 2)) (equal? (cadr g) (caddr g)) (matcho4? (conj-rhs (cadr g))) (proxy? (conj-lhs (cadr g))) (equal? (matcho4-vars (conj-rhs (cadr g))) (list x3)))))

 ;; Negated matcho
 (tassert "match noto pattern fail" (run1 x1 (== x1 `(1 . 2)) (noto (matcho3 ([x1 (2 . y)]) succeed))) '(1 . 2))
 (tassert "match noto pattern succeed" (run1 x1 (== x1 `(1 . 2)) (noto (matcho3 ([x1 (1 . y)]) succeed))) (void))
 (tassert "match noto pattern disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho3 ([x1 (1 . y)]) succeed))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
 (tassert "match noto contents disequality" (run1 (x1 x2) (== x1 `(,x2 . 2)) (noto (matcho3 ([x1 (y . 2)]) (== 1 y)))) `((,(=/= x2 1) . 2) ,(=/= x2 1)))
 (tassert "match noto optimized pair disequality" (run1 (x1 x2 x3) (== x1 `(,x2 . ,x3)) (noto (matcho3 ([x1 (y . z)]) (conde [(== y 1)] [(== z 2)])))) (list (cons (=/= x2 1) (=/= x3 2)) (=/= x2 1) (=/= x3 2)))



 ;; New-style matcho
 ;(display (expand '(matcho3 (['() ()]) succeed)))
; (display (expand '(matcho3 (['() ()] ['() ()]) succeed)))

 

 ;(display (matcho-tst c c))
 (tassert "match no patterns" (matcho3 () succeed) succeed)
 (tassert "match empty list" (matcho3 (['() ()]) succeed) succeed)
 (tassert "match number" (matcho3 ([1 1]) succeed) succeed)
 (tassert "match simple variable rename" (matcho3 ([1 a]) (== x1 a)) (== x1 1))
 (tassert "match multiple empty list" (matcho3 (['() ()] ['() ()]) succeed) succeed)

 ;(trace sc-expand)
 ;(display (matcho-tst #'(matcho-tst 4)))
#;
 (parameterize ([expand-output (current-output-port)]
                [current-expand (trace-lambda expander (x) (sc-expand x))]
                )
   ;(display (matcho6 #'(matcho6 () succeed)))
   (pretty-print (matcho5 (cadddr (matcho5 (caddr (caddr (matcho5 (cadr (caddr (caddr (matcho5 (matcho6 #'(matcho6 (['(1 . 2) (a . d)]) (cons d a))))))))))))))
   ;(matcho5 #'(matcho5 (['(1 . 2) (a . d)]) (cons d a)))
   #;
 (expand `(matcho3 (['(1 . 2) (a . d)]) (cons d a))))
 
 ;(printf "~%")
 #;
 (pretty-print
  (matcho5 (matcho6 #'(matcho6 (['one 'one]) succeed)))
  ;(matcho5 #'(matcho5 () () #f (['() ()]) succeed))

 ; (matcho5 (cadar (cadr (matcho6 #'(matcho6 (['() ()]) succeed)))))
  ;(matcho5 (cadr (caadr (cadddr (caddr (matcho5 (cadar (cadr (matcho6 #'(matcho6 (['() ()]) succeed))))))))))
  )
 

 (begin
   (tassert "match ground pair" (matcho3 (['(1 . 2) (a . d)]) (== x1 (cons d a))) (== x1 '(2 . 1)))
   (tassert "match non-pair fail" (matcho3 ([1 (a . d)]) succeed) fail)
   (tassert "match ground car fail" (matcho3 (['(1 . 2) (2 . d)]) succeed) fail)
   (tassert "match ground cdr fail" (matcho3 (['(1 . 2) (a . 1)]) succeed) fail)
   (tassert "match ground car succeed" (matcho3 (['(1 . 2) (1 . d)]) (== x1 d)) (== x1 2))
   (tassert "match ground cdr succeed" (matcho3 (['(1 . 2) (a . 2)]) (== x1 a)) (== x1 1))
   (tassert "match ground symbol car fail" (matcho3 (['(one . two) ('two . d)]) (== x1 d)) fail)
   (tassert "match ground symbol car succeed" (matcho3 (['(one . two) ('one . d)]) (== x1 d)) (== x1 'two))

   (tassert "match nested car" (matcho3 (['((1 . 3) . 2) ((a . b) . d)]) (== x1 (list a d b))) (== x1 '(1 2 3)))
   (tassert "match nested list" (matcho3 (['((1 . 2)) ((a . b))]) (== x1 (cons b a))) (== x1 '(2 . 1)))
   (tassert "match nested list var" (let ([xs '((1 . 2))]) (matcho3 ([xs ((a . b))]) (== x1 (cons b a)))) (== x1 '(2 . 1))) 
   (tassert "match shared varname" (matcho3 ([1 a] [2 a]) succeed) fail)
   (tassert "match free" (matcho4-vars (matcho3 ([x1 (a . d)]) (cons d a))) (list x1))
   (tassert "match free expand" ((matcho4-procedure (matcho3 ([x1 (a . d)]) (== x2 (cons d a)))) '(1 . 2)) (list succeed (== x2 '(2 . 1))))
   (tassert "match free expand quote" ((matcho4-procedure (matcho3 ([x1 ('one . d)]) (== x2 d))) '(one . 2)) (list succeed (== x2 2)))
   )
 
 

 
 )
