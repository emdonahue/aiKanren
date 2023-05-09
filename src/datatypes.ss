;TODO delete datatypes.ss
(library (datatypes)
  (export make-var var? var-id var-equal?
	  succeed fail succeed? fail?
	  make-state empty-state state? set-state-substitution state-constraints state-substitution state-varid increment-varid instantiate-var set-state-constraints
	  failure failure? guarded? answer? state-or-failure?
	  make-constraint constraint? empty-constraint empty-constraint-store set-disequality constraint-store? constraint-store-constraints make-constraint-store constraint-disequality
	  satisfied satisfied? unsatisfiable unsatisfiable?
	  make-absento absento?
	  =/= =/=? =/=-lhs =/=-rhs disequality? empty-disequality disequality-null?
	  make-substitution empty-substitution substitution-dict substitution?
	  absento)
  (import (chezscheme) (sbral))

  ;; === VAR ===
  (define-structure (var id))
  (define var-equal? equal?)
  
  ;; === STREAMS ===
  (define failure '())
  (define failure? null?)
  
  ;; === GOALS ===
  
  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

    ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints))
  (define-structure (constraint disequality type absento))
  (define-structure (absento atom term))
  (define empty-constraint (make-constraint '() #f succeed))
  (define empty-constraint-store (make-constraint-store '()))
  (define (set-disequality c d)
    (assert (and (constraint? c) (disequality? d)))
    (let ([c (vector-copy c)])
      (set-constraint-disequality! c d) c))
 (define satisfied (make-constraint 'satisfied '_ '_))
  (define (satisfied? c) (eq? c satisfied)) ;TODO rename constraint so that constraint? can include non-structure elements such as satisfied/unsatisfiable
  (define unsatisfiable (make-constraint 'unsatisfiable '_ '_))
  (define (unsatisfiable? c) (eq? c unsatisfiable))

    ;; === SUBSTITUTION ===
  (define-structure (substitution dict))
  (define empty-substitution (make-substitution sbral-empty))
  
  ;; === STATE ===
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

  (define (increment-varid s)
    (assert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))

  (define (state-or-failure? s) (or (state? s) (failure? s)))

  (define (instantiate-var s)
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === STREAMS ===

  (define (answer? s)
    (and (state? s) (null? (state-guards s))))
  
  (define (guarded? s)
    (and (state? s) (not (null? (state-guards s)))))
    
  ;; === ABSENTO ===
  (define absento make-absento)

  ;; === DISEQUALITY ===
  (define-values (empty-disequality disequality? disequality-car disequality-cdr disequality-null?)
    (values '() list? car cdr null?))
  (define-structure (=/= lhs rhs))
  (define =/= make-=/=)
)
