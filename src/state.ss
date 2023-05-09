(library (state)
  (export reify unify instantiate-var walk disunify)
  (import (chezscheme) (except (substitution) unify walk) (prefix (only (substitution) unify walk) substitution:) (var) (failure) (values) (constraints) (negation) (datatypes))
  
  (define (reify s v)
    (cond
     [(pair? v) (cons (reify s (car v)) (reify s (cdr v)))]
     [(var? v)
      (let ([v (substitution:walk (state-substitution s) v)])
	(if (var? v) (get-constraint (state-constraints s) v v)
	    (reify s v)))]
     [else v]))

  (define (extensions->goal es)
    (conj (map (lambda (e) (== (car e) (cdr e))) es)))
  
  (define (unify s x y)
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])
      (run-constraints (set-state-substitution s sub) extensions)))

  (define (run-constraints s cs)
    (assert (state-or-failure? s))
    (if (or (failure? s) (null? cs)) s
	(let ([c (get-constraint (state-constraints s) (caar cs) satisfied)])
	  (run-constraints (run-constraint s c) (cdr cs)))))

  (define (run-constraint s c)
    ;;TODO make use of binding information to short circuit walks on first var in each constraint
    (assert (and (state-or-failure? s) (constraint? c))) ; -> state-or-failure?
    (cond
     [(satisfied? c) s]
     [(unsatisfiable? c) failure]
     [else (run-disequalities s (constraint-disequality c))]))

  (define (run-disequalities s ds) ; Disjunction of conjunctions of primitive disequalities.
    (assert (and (state-or-failure? s) (list? ds))) ; -> state-or-failure?
    (if (or (failure? s) (null? ds)) s
	(run-disequalities
	 (run-disequality s (car ds)) (cdr ds))))

  (define (run-disequality s d) ; Conjunction of primitive disequalities.
    (assert (and (state-or-failure? s) (list? d))) ; -> state-or-failure?
    (if (or (failure? s) (disequality-null? d)) s
	(run-disequality (disunify s (caar d) (cdar d)) (cdr d))))
   
  (define (disunify s x y)
    (assert (state? s))			; -> state-or-failure?
    (let-values ([(sub extensions) (substitution:unify (state-substitution s) x y)])
      (printf "EXT: ~s~%" (extensions->goal extensions))
      (printf "NEGATED: ~s~%" (noto (extensions->goal extensions)))
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

  ;; === CONSTRAINTS ===
   
  (define (add-disequality s v d)
    (assert (and (state? s) (var? v) (disequality? d)))
    (set-state-constraints s (merge-disequality (state-constraints s) v d))))
