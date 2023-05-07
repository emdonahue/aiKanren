(library (state)
  (export make-state empty-state state? reify unify instantiate-var set-state-substitution walk guarded? answer? disunify)
  (import (chezscheme) (except (substitution) unify walk) (prefix (only (substitution) unify walk) substitution:) (var) (failure))

  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution #f '() #f 0))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) failure))

  (define (answer? s)
    (and (state? s) (null? (state-guards s))))
  
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

   (define (disunify s x y)
     3)

   (define (walk s v)
     (substitution:walk (state-substitution s) v))
   
   (define (instantiate-var s)
     (values (make-var (state-varid s)) (increment-varid s))))
