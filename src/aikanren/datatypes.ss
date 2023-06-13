;TODO delete datatypes.ss
(library (datatypes)
  (export simplification-level
	  make-runner runner? runner-stream runner-query runner-package set-runner-stream
	  package? empty-package
	  make-var var? var-id var-equal?
	  stream?
	  failure failure?
	  make-bind bind? bind-goal bind-stream
	  make-mplus mplus? mplus-lhs mplus-rhs
	  make-answers answers? answers-car answers-cdr
	  answer? state-or-failure?
	  empty-state state? state-substitution state-constraints state-varid set-state-substitution set-state-constraints set-state-varid increment-varid instantiate-var
	  empty-substitution
	  make-constraint-store constraint-store? constraint-store-constraints empty-constraint-store
	  make-constraint constraint? constraint-goal set-constraint-goal
	  goal? goal-cond
	  succeed fail succeed? fail?
	  == ==? ==-lhs ==-rhs
	  fresh?
	  make-conj conj conj? conj-car conj-cdr conj* conj-fold
	  disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs
	  pconstraint? pconstraint pconstraint-vars pconstraint-procedure
	  guardo? make-guardo guardo-var guardo-procedure guardo
	  make-noto noto? noto-goal)
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

  ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints)) ; Constraints are represented as a list of pairs in which car is the attributed variable and cdr is the goal representing the constraint
  (define empty-constraint-store (make-constraint-store '()))

  (define-structure (constraint goal))
  (define (set-constraint-goal c g)
    (assert (and (constraint? c) (goal? g)))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))
  
  (define-structure (pconstraint vars procedure))
  (define (pconstraint vars procedure)
    (make-pconstraint (if (list? vars) vars (list vars)) procedure))
  
  (define-structure (guardo var procedure))
  (define guardo make-guardo)

  ;; === SUBSTITUTION ===
  (define empty-substitution sbral-empty)
  
  ;; === STATE ===
  (define-structure (state substitution constraints pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store #f 1))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (assert (and (state? s) (constraint-store? c)))
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))

  (define (increment-varid s)
    (assert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (fx1+ (state-varid s))) s))

  (define (set-state-varid s v)
    ;;TODO remove set-state-varid
    (assert (and (state? s) (number? v) (fx<= (state-varid s) v)))
    (if (fx= (state-varid s) v) s
	(let ([s (vector-copy s)])
	  (set-state-varid! s v) s)))

  (define (state-or-failure? s) (or (state? s) (failure? s)))

  (define (instantiate-var s)
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === STREAMS ===
  (define failure '(failure))
  (define (failure? s) (eq? s failure))
  
  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (answers car cdr))

  (define answer? state?)
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (bind? s) (bind? s) (answer? s) (answers? s)))
  
  ;; === GOALS ===
  (define-values (succeed fail) (values (vector 'succeed) (vector 'fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  (define-structure (noto goal)) ; Negated goal

  (define == make-==)

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g) (pconstraint? g) (guardo? g)))

  (define-syntax goal-cond ;TODO delete goal-cond
    (syntax-rules ()
      [(_ goal clauses ...)
       (case (if (procedure? goal) 'fresh (vector-ref goal 0))
	 clauses ...)]))
  
  ;; CONJ
  (define (conj lhs rhs) ;TODO replace conj with make-conj where possible
    (assert (and (goal? lhs) (goal? rhs)))
    (cond
     [(or (fail? lhs) (fail? rhs)) fail]
     [(succeed? rhs) lhs]
     [(succeed? lhs) rhs]
     ;[(and (or (fresh? lhs) (disj? lhs)) (not (or (fresh? rhs) (disj? rhs)))) (make-conj rhs lhs)] ;TODO evaluate divergence avoidance in conj goals
     [else (make-conj lhs rhs)]))

  (define (conj* . conjs)
    (fold-right (lambda (lhs rhs) (conj lhs rhs)) succeed conjs))
  
  (define (conj-car c)
    (assert (conj? c))
    (conj-lhs c))
  
  (define (conj-cdr c)
    (assert (conj? c))
    (conj-rhs c))
  
  (define (conj-fold p s cs) ;TODO is conj-fold ever used?
    (assert (and (procedure? p) (conj? cs)))
    (let ([lhs (if (conj? (conj-lhs cs))
		   (conj-fold p s (conj-lhs cs))
		   (p s (conj-lhs cs)))])
      (if (conj? (conj-rhs cs))
	  (conj-fold p lhs (conj-rhs cs))
	  (p lhs (conj-rhs cs)))))

  ;; DISJ
  (define (disj lhs rhs)
    (assert (and (goal? lhs) (goal? rhs)))
    (cond
     [(or (succeed? lhs) (succeed? rhs)) succeed]
     [(fail? rhs) lhs]
     [(fail? lhs) rhs]
     [else (make-disj lhs rhs)]))

  (define (disj* . disjs)
    (fold-right (lambda (lhs rhs) (disj lhs rhs)) fail disjs))

  (define (disj-car c)
    (if (disj? c)
	(disj-lhs c)
	#;
	(disj-car (disj-lhs c)) c))

  (define (disj-cdr c)
    (if (disj? c)
	(disj-rhs c)
	#;
	(disj (disj-cdr (disj-lhs c)) (disj-rhs c)) fail)))
