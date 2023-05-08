(library (state)
  (export make-state empty-state state? reify unify instantiate-var set-state-substitution walk guarded? answer? disunify state-or-failure?)
  (import (chezscheme) (except (substitution) unify walk) (prefix (only (substitution) unify walk) substitution:) (var) (failure) (values) (constraints))

  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store '() #f 0))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))

  (define (state-or-failure? s) (or (state? s) (failure? s)))
  
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
     [(var? v)
      (let ([v (substitution:walk (state-substitution s) v)])
	(if (var? v) (get-constraint (state-constraints s) v v)
	    (reify s v)))]
     [else v]))

  (define (unify s x y)
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])
      (run-constraints (set-state-substitution s sub) extensions)))

  (define (run-constraints s cs)
    (assert (state-or-failure? s))
    (if (or (failure? s) (null? cs)) s
	(let ([c (get-constraint (state-constraints s) (caar cs) satisfied)])
	  (run-constraints (run-constraint s c) (cdr cs)))))

  (define (run-constraint s c)
    (assert (and (state? s) (constraint? c)))
    (cond
     [(satisfied? c) s]
     [(unsatisfiable? c) failure]
     [else (run-disequality s (constraint-disequality c))]))

  (define (run-disequality s d)
    (assert (and (state? s) (disequality? d)))
    s)
   
   (define (disunify s x y)
     (assert (state? s)) ; -> state-or-failure?
     (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])
       (cond
	[(failure? sub) s] ; If unification fails, the terms can never be made equal, so no need for constraint: return state as is.
	[(null? extensions) failure] ; If no bindings were added, the terms are already equal and so in violation of =/=. Fail immediately.
	[else
	 (let* ([s (add-disequality s (caar extensions) extensions)]
		[extended-var (cdar extensions)])
	   (if (var? extended-var)
	       (add-disequality s extended-var extensions) s))]
	)))
     

   (define (walk s v)
     (substitution:walk (state-substitution s) v))
   
   (define (instantiate-var s)
     (values (make-var (state-varid s)) (increment-varid s)))

   ;; === CONSTRAINTS ===
   
   (define (add-disequality s v d)
     (assert (and (state? s) (var? v) (disequality? d)))
     (set-state-constraints s (merge-disequality (state-constraints s) v d))))
