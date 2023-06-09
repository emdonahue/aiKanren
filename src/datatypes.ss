;TODO delete datatypes.ss
(library (datatypes)
  (export simplification-level
	  make-runner set-runner-stream runner? runner-stream runner-query runner-package
	  package? empty-package
	  make-==  make-bind answers? stream? answers answers? answers-car answers-cdr bind? bind-goal bind-stream make-mplus mplus? mplus-lhs mplus-rhs
	  make-var var? var-id var-equal?
	  succeed fail succeed? fail?
	  make-state empty-state state? set-state-substitution state-constraints state-substitution state-varid increment-varid instantiate-var set-state-constraints set-state-varid pconstraint? pconstraint pconstraint-vars pconstraint-procedure clear-state-constraints
	  guardo? make-guardo guardo-var guardo-procedure guardo
	  failure failure? guarded? answer? state-or-failure?
	  make-constraint constraint? empty-constraint-store constraint-store? constraint-goal constraint-store-constraints make-constraint-store set-constraint-goal
	  empty-substitution
	  make-== ==? ==-lhs ==-rhs disj make-disj disj* normalized-disj normalized-disj* disj? disj-car disj-cdr disj-disjuncts goal? fresh?
	  conj conj? conj-car conj-cdr conj* conj-fold
	  == make-noto noto? noto-goal)
  (import (chezscheme) (sbral))

  ;; === RUNTIME PARAMETERS ===
  (define simplification-level (make-parameter 2))
  
  ;; === RUNNER ===
  (define-structure (runner stream query package))
  
  (define (set-runner-stream r s)
    (assert (and (runner? r) (not (runner? s))))
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r))

  ;; === PACKAGE ===  
  (define-structure (package tables))
  (define empty-package (make-package '()))
  
  ;; === VAR ===
  (define-structure (var id)) ;TODO make the var tag a unique object to avoid unifying with a (var _) vector and confusing it for a real var
  (define var-equal? equal?)
  
  ;; === STREAMS ===
  (define failure '())
  (define failure? null?)
  (define-structure (mplus lhs rhs)) ;TODO test mplus with just pairs
  (define-structure (bind goal stream))
  (define-values (answers answers? answers-car answers-cdr) (values cons pair? car cdr)) ; A answers stream is one with at least one answer and either more answers or a bind stream. It is represented as an improper list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (bind? s) (bind? s) (answer? s) (guarded? s) (answers? s)))
  
  ;; === GOALS ===
  
  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

    ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints)) ; Constraints are represented as a list of pairs in which car is the attributed variable and cdr is the goal representing the constraint
  (define-structure (constraint goal))
  (define-structure (pconstraint vars procedure))
  (define (pconstraint vars procedure)
    (make-pconstraint (if (list? vars) vars (list vars)) procedure))
  (define empty-constraint-store (make-constraint-store '()))
  (define (set-constraint-goal c g)
    (assert (and (constraint? c) (goal? g)))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))

  (define-structure (guardo var procedure))
  (define guardo make-guardo)

    ;; === SUBSTITUTION ===
  (define empty-substitution sbral-empty)
  
  ;; === STATE ===
  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store '() #f 1))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (assert (and (state? s) (constraint-store? c)))
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))

  (define (clear-state-constraints s) ; TODO instead of clearing constraint store, use non constraint checking unify, then delete clear constraint store fn
    (set-state-constraints s empty-constraint-store))

  (define (increment-varid s)
    (assert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))

  (define (set-state-varid s v)
    (assert (and (state? s) (number? v) (<= (state-varid s) v)))
    (if (= (state-varid s) v) s
	(let ([s (vector-copy s)])
	  (set-state-varid! s v) s)))

  (define (state-or-failure? s) (or (state? s) (failure? s)))

  (define (instantiate-var s)
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === STREAMS ===

  (define (answer? s)
    (and (state? s) (null? (state-guards s))))
  
  (define (guarded? s)
    (and (state? s) (not (null? (state-guards s)))))

  ;; === GOALS ===
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints
  (define-structure (conj lhs rhs))
  (define-structure (disj disjuncts))
  (define-structure (noto goal)) ; Negated goal

  (define == make-==)

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g) (pconstraint? g) (guardo? g)))

  (define (conj lhs rhs)
    (assert (and (goal? lhs) (goal? rhs)))
    (cond
     [(or (fail? lhs) (fail? rhs)) fail]
     [(succeed? rhs) lhs]
     [(succeed? lhs) rhs]
     ;[(and (or (fresh? lhs) (disj? lhs)) (not (or (fresh? rhs) (disj? rhs)))) (make-conj rhs lhs)]
     [else (make-conj lhs rhs)]))
  
  (define (conj* . conjs)
    (fold-right (lambda (lhs rhs) (conj lhs rhs)) succeed conjs))
  
  (define conj-car conj-lhs)
  (define conj-cdr conj-rhs)

  (define (conj-fold p s cs)
    (assert (and (procedure? p) (conj? cs)))
    (let ([lhs (if (conj? (conj-lhs cs))
		   (conj-fold p s (conj-lhs cs))
		   (p s (conj-lhs cs)))])
      (if (conj? (conj-rhs cs))
	  (conj-fold p lhs (conj-rhs cs))
	  (p lhs (conj-rhs cs)))))
  
  (define (disj disjuncts)
    (assert (list? disjuncts))
    ;;TODO move successes to front of disj so they turn into failures if negated
    (cond
     [(null? disjuncts) fail]
     [(null? (cdr disjuncts)) (car disjuncts)]
     [else (make-disj disjuncts)]))

  (define (disj* . disjuncts)
    (disj disjuncts))

  (define (normalized-disj d)
    (let ([d (normalize-disj d)])
      (if (succeed? d) succeed (disj d))))

  (define (normalized-disj* . disjuncts)
    (normalized-disj disjuncts))

  (define (normalize-disj ds)
    (cond
     [(null? ds) '()]
     [(succeed? (car ds)) succeed]
     [else
      (let ([rest (normalize-disj (cdr ds))])
	(cond
	 [(succeed? rest) succeed]
	 [(fail? (car ds)) rest]
	 [(disj? (car ds)) (append (disj-disjuncts (car ds)) rest)]
	 [else (cons (car ds) rest)]))]))

  (define (disj-car d)
    (if (disj? d) (car (disj-disjuncts d)) d))

  (define (disj-cdr d)
    (if (disj? d) (disj (cdr (disj-disjuncts d))) fail)))
