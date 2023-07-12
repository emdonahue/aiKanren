;TODO delete datatypes.ss
(library (datatypes)
  (export simplification-level
	  make-runner runner? runner-stream runner-query runner-package set-runner-stream
	  package? empty-package
	  make-var var? var-id set-var-id!
	  stream?
	  failure failure?
	  make-bind bind? bind-goal bind-stream
	  make-mplus mplus? mplus-lhs mplus-rhs
	  make-answers answers? answers-car answers-cdr
	  answer? state-or-failure?
	  empty-state state? state-substitution state-constraints state-varid set-state-substitution set-state-constraints set-state-varid increment-varid instantiate-var
	  empty-substitution
	  make-constraint-store constraint-store? constraint-store-constraints empty-constraint-store
	  constraint constraint? constraint-goal set-constraint-goal
	  goal? ;goal-cond
	  succeed fail succeed? fail? trivial-goal?
	  == ==? ==-lhs ==-rhs
	  fresh? make-exist exist? exist-procedure
	  make-conj conj conj? conj-car conj-cdr conj-lhs conj-rhs conj* conj-memp conj-fold conj-filter ;TODO replace conj-car/cdr with lhs/rhs
	  make-disj disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs disj-succeeds?
	  conde-disj conde? conde-lhs conde-rhs conde->disj
	  pconstraint? pconstraint pconstraint-vars pconstraint-procedure pconstraint-type
	  guardo? guardo-var guardo-procedure guardo
	  make-matcho matcho? matcho-out-vars matcho-in-vars matcho-goal expand-matcho normalize-matcho
	  make-noto noto? noto-goal
	  __
	  debug-goal debug-goal? debug-goal-goal)
  (import (chezscheme) (sbral) (utils))

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

  ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints)) ; Constraints are represented as a list of pairs in which car is the attributed variable and cdr is the goal representing the constraint
  (define empty-constraint-store (make-constraint-store '()))

  (define-structure (constraint goal))
  (define (constraint g)
    (if (or (fail? g) (succeed? g)) g (make-constraint g)))
  (define (set-constraint-goal c g)
    (assert (and (constraint? c) (goal? g)))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))
  
  (define-structure (pconstraint vars type procedure))
  (define (pconstraint vars type procedure)
    (assert (and (or (var? vars) (list? vars)) (procedure? procedure)))
    (make-pconstraint (if (list? vars) vars (list vars)) type procedure))
  
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
  (define failure (vector 'failure))
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
  (define (trivial-goal? g) (or (fail? g) (succeed? g)))
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  (define-structure (conde lhs rhs))
  (define-structure (noto goal)) ; Negated goal
  (define-structure (exist procedure))

  (define (== x y)
    (cond
     [(or (eq? x __) (eq? y __)) succeed]
     [(or (var? x) (var? y)) (make-== x y)]
     [(equal? x y) succeed]
     [(and (pair? x) (pair? y)) (make-== x y)]
     [else fail]))

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.

  (define-structure (matcho out-vars in-vars goal))
  (org-define (normalize-matcho out in proc) ;TODO see if normalize-matcho adds anything to solve-matcho
    (if (or (null? out) (var? (car out))) (make-matcho out in proc) (normalize-matcho (cdr out) (cons (car out) in) proc)))

  (org-define (expand-matcho g s p)
    ((matcho-goal g) s p (matcho-in-vars g)))
  
  (define (goal? g)
    (or (matcho? g) (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g) (pconstraint? g) (guardo? g) (conde? g) (exist? g) (debug-goal? g)))

  #;
  (define-syntax goal-cond ;TODO revisit goal-cond once fresh is either explicit or removed
    (syntax-rules ()
      [(_ goal (predicate body ...) ...)
       (case (if (procedure? goal) 'fresh (vector-ref goal 0))
	 clauses ...)]))

  (define (conde-disj x y)
    ;; Conde can simplify on failure, but unlike disj constraints, cannot simply remove itself on success.
    (cond
     [(fail? x) y]
     [(fail? y) x]
     [else (make-conde x y)]))

  (define-structure (debug-goal name goal))
  (define debug-goal make-debug-goal)
  
  ;; CONJ


  (define (conj lhs rhs) ;TODO replace conj with make-conj or short circuiting conj* where possible
    (assert (and (goal? lhs) (goal? rhs)))
    (cond
     [(or (fail? lhs) (fail? rhs)) fail]
     [(succeed? rhs) lhs]
     [(succeed? lhs) rhs]
     [else (make-conj lhs rhs)]))

  (define-syntax conj* ;TODO experiment with short circuiting conj and disj macros
    (syntax-rules () ;TODO make conj a macro but when it is just an identifier macro make it return a function of itself for use with higher order fns
      [(_) succeed]
      [(_ g) g]
      [(_ lhs rhs ...) (conj lhs (conj* rhs ...))
       #;
       (let ([l lhs])
	 (if (fail? l) fail
	     (let ([r (conj* rhs ...)])
	       (cond
		[(fail? r) r]
		[else (make-conj l r)]))))]))

  #;
  (define (conj* . conjs)
    (fold-right (lambda (lhs rhs) (conj lhs rhs)) succeed conjs))
  
  (define (conj-car c)
    (assert (conj? c))
    (conj-lhs c))
  
  (define (conj-cdr c)
    (assert (conj? c))
    (conj-rhs c))

  (define (conj-filter c p)
    (if (conj? c)
	(conj
	 (conj-filter (conj-lhs c) p)
	 (conj-filter (conj-rhs c) p))
	(if (p c) c succeed)))

  (define (conj-memp c p)
    (if (conj? c)
	(or (conj-memp (conj-lhs c) p) (conj-memp (conj-rhs c) p))
	(if (p c) c #f)))
  
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

  (define (disj-car g)
    (if (disj? g)
	(disj-car (disj-lhs g))
	g))

  (define (disj-cdr g)
    (if (disj? g)
	(disj (disj-cdr (disj-lhs g)) (disj-rhs g))
	fail))

  (define (conde->disj c)
    (if (conde? c) (disj (conde->disj (conde-lhs c)) (conde->disj (conde-rhs c))) c))
  
  (define (disj-succeeds? d)
    ;; True if d contains a literal succeed goal.
    (cond
     [(succeed? d) #t]
     [(disj? d) (or (disj-succeeds? (disj-lhs d)) (disj-succeeds? (disj-rhs d)))]
     [else #f]))

  ;; === QUANTIFICATION ===

  (define __ (vector '__)))
