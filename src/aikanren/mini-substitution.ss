					;TODO remove mini-substitution
(library (mini-substitution)
  (export mini-walk mini-unify mini-reify)
  (import (chezscheme) (datatypes))


  (define (mini-walk s v)
    (if (var? v)
	(let ([b (assq v s)])
	  (if b (mini-walk s (cdr b)) v))
	v))

  (define (mini-reify s v)
    (exclusive-cond
     [(pair? v) (cons (mini-reify s (car v)) (mini-reify s (cdr v)))]
     [(var? v)
      (let ([v^ (mini-walk s v)])
	(if (eq? v v^) v (mini-reify s v^)))]
     [else v]))

  (define (mini-unify s x y)
    (let ([x (mini-walk s x)] [y (mini-walk s y)])
      (cond
       [(eq? x y) s]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
	(mini-unify (mini-unify s (car x) (car y)) (cdr x) (cdr y))]
       [else failure])))

  (define (extend s x y)
    (cons (cons x y) s)))
