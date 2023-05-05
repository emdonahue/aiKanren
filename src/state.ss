(library (state)
  (export make-state empty-state state? reify unify instantiate-var set-state-substitution walk guarded?)
  (import (chezscheme) (except (substitution) unify walk) (prefix (only (substitution) unify walk) substitution:) (var))

  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution #f '() #f 0))

  (define (set-state-substitution s substitution)
    (if substitution
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) #f))

  (define (guarded? s)
    (and (state? s) (not (null? (state-guards s)))))
  
  
  (define (increment-varid s)
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v) (reify s (substitution:walk (state-substitution s) v))]
     [else v]))

   (define (unify s x y)
     (set-state-substitution s (substitution:unify (state-substitution s) x y)))

   (define (walk s v)
     (substitution:walk (state-substitution s) v))
   
   (define (instantiate-var s)
     (values (make-var (state-varid s)) (increment-varid s))))
