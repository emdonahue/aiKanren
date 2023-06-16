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
    (mini-walk s v))

  (define (mini-unify s x y)
    (let ([x (mini-walk s x)] [y (mini-walk s y)])
      (cond
       [(failure? s) failure]
       [(eq? x y) s]
       [(and (var? x) (var? y))
	(cond
	 [(fx< (var-id x) (var-id y)) (extend s x y)]
	 [(var-equal? x y)
	  (assert #f)
	  s] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
	 [else (extend s y x)])]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
	(mini-unify (mini-unify s (car x) (car y)) (cdr x) (cdr y))]
       [else failure])))

  (define (extend s x y)
    (cons (cons x y) s)))
