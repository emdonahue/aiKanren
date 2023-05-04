(library (state)
  (export make-state empty-state state? reify state-substitution unify instantiate-var set-state-substitution walk state-guarded?)
  (import (chezscheme) (substitution))

  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state substitution-empty #f '() #f 0))

  (define (set-state-substitution s substitution)
    (if substitution
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) #f))

  (define (state-guarded? s)
    (not (null? (state-guards s))))
  
  
  (define (increment-varid s)
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v) (reify s (substitution-walk (state-substitution s) v))]
     [else v]))

   (define (unify s x y)
     (cond
      [(not s) #f]
      [(state? s) (set-state-substitution s (unify (state-substitution s) x y))]
      [else (let ([x (substitution-walk s x)] [y (substitution-walk s y)])
	      (cond
	       [(eq? x y) s]
	       [(and (var? x) (var? y))
		(cond
		 [(< (var-id x) (var-id y)) (extend s x y)]
		 [(= (var-id x) (var-id y)) s] ; Usually handled by eq? but for serialized or other dynamically constructed vars, this is a fallback.
		 [else (extend s y x)])]
	       [(var? x) (extend s x y)]
	       [(var? y) (extend s y x)]
	       [(and(pair? x) (pair? y))
		(unify (unify s (car x) (car y)) (cdr x) (cdr y))]
	       [else #f]))]))

   (define (walk s v)
     (substitution-walk (state-substitution s) v))
   
   (define (instantiate-var s)
     (values (make-var (state-varid s)) (increment-varid s))))
