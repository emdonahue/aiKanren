(library (state)
  (export make-state empty-state state? reify state-substitution unify)
  (import (chezscheme) (substitution))

  (define-structure (state substitution))
  (define empty-state (make-state substitution-empty))

  (define (set-state-substitution s substitution)
    (if substitution
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) #f))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v) (reify s (walk (state-substitution s) v))]
     [else v]))

   (define (unify s x y)
     (cond
      [(not s) #f]
      [(state? s) (set-state-substitution s (unify (state-substitution s) x y))]
      [else (let ([x (walk s x)] [y (walk s y)])
	      (cond
	       [(eq? x y) s]
	       [(and (var? x) (var? y))
		(if (< (var-id x) (var-id y)) (extend s x y)
		    (extend s y x))]
	       [(var? x) (extend s x y)]
	       [(var? y) (extend s y x)]
	       [(and(pair? x) (pair? y))
		(unify (unify s (car x) (car y)) (cdr x) (cdr y))]
	       [else #f]))])))
