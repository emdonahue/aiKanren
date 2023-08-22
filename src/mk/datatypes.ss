;TODO delete datatypes.ss
(library (datatypes)
  (export lazy-solver reify-constraints
	  make-runner runner? runner-stream runner-query runner-package set-runner-stream
	  package? empty-package
	  var make-var var? var-id set-var-id!
	  stream?
	  failure failure?
	  make-bind bind? bind-goal bind-stream
	  make-mplus mplus? mplus-lhs mplus-rhs
	  make-answers answers? answers-car answers-cdr
	  answer? state-or-failure?
	  empty-state state? state-substitution state-constraints state-varid set-state-substitution set-state-constraints set-state-varid increment-varid instantiate-var state-extend-store
	  empty-substitution
	  make-constraint-store constraint-store? constraint-store-constraints empty-constraint-store
	  constraint constraint? constraint-goal set-constraint-goal proxy proxy-constraint? proxy-constraint-constraint
	  goal? goal-memp
	  succeed fail succeed? fail?
	  make-== == ==? ==-lhs ==-rhs
	  fresh? make-exist exist? exist-procedure
	  make-conj conj conj? conj-car conj-cdr conj-lhs conj-rhs conj* conj-memp conj-fold conj-filter conj-diff conj-member conj-intersect ;TODO replace conj-car/cdr with lhs/rhs
	  make-disj disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs disj-succeeds? disj-factorize disj-factorized
	  conde-disj conde? conde-lhs conde-rhs conde-car conde-cdr conde->disj
	  pconstraint? pconstraint pconstraint-vars pconstraint-data pconstraint-procedure pconstraint-rebind-var pconstraint-check pconstraint-attributed?
	  make-matcho matcho? matcho-out-vars matcho-in-vars matcho-goal expand-matcho normalize-matcho matcho-attributed? matcho-test-eq?
	  make-noto noto? noto-goal
	  __
	  make-trace-goal trace-goal? trace-goal-name trace-goal-source trace-goal-goal make-untrace-goal untrace-goal? untrace-goal-goal
	  prove proof-goal? proof-goal-goal proof-goal-proof)
  (import (chezscheme) (sbral) (utils))

  ;; === RUNTIME PARAMETERS ===
  (define lazy-solver (make-parameter #t))
  (define reify-constraints (make-parameter #t))
  
  ;; === RUNNER ===
  (define-structure (runner stream query package))
  
  (define (set-runner-stream r s)
    (cert (runner? r) (not (runner? s)))
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r))

  ;; === PACKAGE ===  
  (define-structure (package tables))
  (define empty-package (make-package '()))
  
  ;; === VAR ===
  (define-structure (var id)) ;TODO make the var tag a unique object to avoid unifying with a (var _) vector and confusing it for a real var
  (define var make-var)

  ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints)) ; Constraints are represented as a list of pairs in which car is the attributed variable and cdr is the goal representing the constraint
  (define empty-constraint-store (make-constraint-store '()))

  (define-structure (constraint goal))
  (define (constraint g)
    (if (or (fail? g) (succeed? g)) g (make-constraint g)))
  (define (set-constraint-goal c g)
    (cert (constraint? c) (goal? g))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))
  
  (define-structure (pconstraint vars procedure data))
  (define (pconstraint vars procedure data)
    (cert (list? vars) (procedure? procedure))
    (make-pconstraint vars procedure data))

  (define pconstraint-rebind-var
    ;; Moves a pconstraint from one var to another
    (case-lambda
      [(g v) (pconstraint (cons v (cdr (pconstraint-vars g)))
			  (pconstraint-procedure g)
			  (pconstraint-data g))]
      [(g v v^) (if (eq? v v^) g
		    (pconstraint (cons v^ (remq v (pconstraint-vars g)))
				 (pconstraint-procedure g)
				 (pconstraint-data g)))]))

  (define (pconstraint-check p var val)
    (cert (memq var (pconstraint-vars p)))
    ((pconstraint-procedure p) var val succeed succeed (pconstraint-data p)))

  (define (pconstraint-attributed? p var)
    (memq var (pconstraint-vars p)))

  (define-structure (proxy-constraint constraint))
  (define (proxy g)
    (cert (goal? g))
    (make-proxy-constraint g))

  ;; === SUBSTITUTION ===
  (define empty-substitution sbral-empty)
  
  ;; === STATE ===
  (define-structure (state substitution constraints pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store #f 1))

  (define (set-state-substitution s substitution) ;TODO try replacing state vector copy with manual updates using mutators
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (cert (state? s) (constraint-store? c))
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))
  (define (state-extend-store s g)
    (make-state (state-substitution s) (cons g (state-constraints s)) (state-pseudocounts s) (state-varid s)))
  
  (define (increment-varid s)
    (cert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (fx1+ (state-varid s))) s))

  (define (set-state-varid s v)
    ;;TODO remove set-state-varid
    (cert (state? s) (number? v) (fx<= (state-varid s) v))
    (if (fx= (state-varid s) v) s
	(let ([s (vector-copy s)])
	  (set-state-varid! s v) s)))

  (define (state-or-failure? s) (or (state? s) (failure? s))) ;TODO rename state-or-failure? to maybe-state?

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
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints. also break two pairs into a conj of ==. then we can simplify the order checking inside the unifier
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  (define-structure (noto goal)) ; Negated goal
  (define-structure (exist procedure))

  (define (== x y)
    (cond
     [(or (eq? x __) (eq? y __)) succeed]
     [(or (var? x) (var? y)) (make-== x y)] ;TODO == should put vars first so it has a better chance of simplifying in the ctn
     [(equal? x y) succeed]
     [(and (pair? x) (pair? y)) (make-== x y)] ;TODO the double pair case for == should factorize into a conj of ==. this can then simplify the unifier's order checking
     [else fail]))
  
  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.

  (define-structure (matcho out-vars in-vars goal))
  
  (define (normalize-matcho out in proc) ;TODO see if normalize-matcho adds anything to solve-matcho
    (cert (not (and (null? out) (null? in))))
    (if (or (null? out) (var? (car out))) (make-matcho out in proc)
	(if (pair? (car out)) (normalize-matcho (cdr out) (cons (car out) in) proc) fail)))

  (define (expand-matcho g s p)
    ((matcho-goal g) s p (matcho-in-vars g)))

  (define (matcho-attributed? g var)
    (memq var (matcho-out-vars g)))

  (define (matcho-test-eq? g out in) ; Shorthand for checking the comparable properties of matcho during unit testing.
    (and (matcho? g) (equal? (matcho-out-vars g) out) (equal? (matcho-in-vars g) in)))
  
  (define (goal? g)
    (or (matcho? g) (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g) (pconstraint? g) (conde? g) (exist? g) (proxy-constraint? g) (trace-goal? g) (proof-goal? g) (untrace-goal? g)))

  (define goal-memp
    (case-lambda
      [(g p) (goal-memp g  p '())]
      [(g p gs)
       (cond
	[(p g) (cons g gs)]
	[(conj? g) (let ([gs (goal-memp (conj-rhs g) p gs)])
		     (goal-memp (conj-lhs g) p gs))]
	[(disj? g) (let ([gs (goal-memp (disj-rhs g) p gs)])
		     (goal-memp (disj-lhs g) p gs))]
	[else gs])]))

  #;
  (define-syntax goal-cond ;TODO revisit goal-cond once fresh is either explicit or removed
    (syntax-rules ()
      [(_ goal (predicate body ...) ...)
       (case (if (procedure? goal) 'fresh (vector-ref goal 0))
	 clauses ...)]))

  (define-structure (conde lhs rhs))

  (define-structure (untrace-goal goal)) ; Used internally in cps tracing interpreters to manipulate the nesting of the proofs.

  (define (conde-car g)
    (if (conde? g)
	(conde-car (conde-lhs g))
	g))

  (define (conde-cdr g)
    (if (conde? g)
	(let ([lhs (conde-cdr (conde-lhs g))])
	  (if (fail? lhs) (conde-rhs g) (make-conde lhs (conde-rhs g))))
	fail))
  
  (define (conde-disj x y)
    ;; Conde can simplify on failure, but unlike disj constraints, cannot simply remove itself on success.
    (cond
     [(fail? x) y]
     [(fail? y) x]
     [else (make-conde x y)]))

  (define-structure (trace-goal name source goal))
  (define-structure (proof-goal proof goal))
  (define-syntax prove
    (syntax-rules ()
      [(_ proof g ...)
       (make-proof-goal 'proof (conj* g ...))]))
  
  ;; CONJ
  (define (conj lhs rhs) ;TODO replace conj with make-conj or short circuiting conj* where possible
    (when (not (goal? lhs)) (display lhs))
    (cert (goal? lhs) (goal? rhs))
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
  
  (define (conj-car c) ;TODO remove conj-car
    (cert (conj? c))
    (conj-lhs c))
  
  (define (conj-cdr c)
    (cert (conj? c))
    (conj-rhs c))

  (define (conj-filter c p)
    (if (conj? c)
	(conj
	 (conj-filter (conj-lhs c) p)
	 (conj-filter (conj-rhs c) p))
	(if (p c) c succeed)))

  (define (conj-diff c d)
    (if (conj? c) (conj (conj-diff (conj-lhs c) d) (conj-diff (conj-rhs c) d))
	(if (conj-member c d) succeed c)))

  (define (conj-intersect c d)
    (if (conj? c) (conj (conj-intersect (conj-lhs c) d) (conj-intersect (conj-rhs c) d))
	(if (conj-member c d) c succeed)))

  (define (conj-member e c)
    (if (conj? c) (or (conj-member e (conj-lhs c)) (conj-member e (conj-rhs c)))
	(equal? c e)))

  (define (conj-memp c p)
    (if (conj? c)
	(or (conj-memp (conj-lhs c) p) (conj-memp (conj-rhs c) p))
	(if (p c) c #f)))
  
  (define (conj-fold p s cs) ;TODO is conj-fold ever used?
    (cert (procedure? p) (conj? cs))
    (let ([lhs (if (conj? (conj-lhs cs))
		   (conj-fold p s (conj-lhs cs))
		   (p s (conj-lhs cs)))])
      (if (conj? (conj-rhs cs))
	  (conj-fold p lhs (conj-rhs cs))
	  (p lhs (conj-rhs cs)))))

  ;; DISJ
  (define (disj lhs rhs) ;TODO convert constructor fns to constructed params of structure  
    (cert (goal? lhs) (goal? rhs))
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

  (define (disj-cdr g) ;TODO microbenchmark disj cdr that looks ahead instead of using base case to check for non disj
    (if (disj? g)
	(disj (disj-cdr (disj-lhs g)) (disj-rhs g))
	fail))

  (define conde->disj
    ;; Inverts conde from right-branching to left-branching to allow for optimizations in solve-disj
    (case-lambda
      [(c) (conde->disj c fail)]
      [(c d) (if (conde? c) (conde->disj (conde-rhs c) (conde->disj (conde-lhs c) d)) (disj d c))]))
  
  (define (disj-succeeds? d)
    ;; True if d contains a literal succeed goal.
    (cond
     [(succeed? d) #t]
     [(disj? d) (or (disj-succeeds? (disj-lhs d)) (disj-succeeds? (disj-rhs d)))]
     [else #f]))

  (org-define (disj-factorize lhs rhs)
    (let ([intersection (conj-intersect lhs rhs)])
      (org-display intersection)
      (values (conj-filter intersection (lambda (c) (not (disj? c))))
	      (conj-filter intersection disj?)
	      (conj-diff lhs intersection)
	      (conj-diff rhs intersection))))

  (define (disj-factorized lhs rhs)
    (let-values ([(cs ds lhs rhs) (disj-factorize lhs rhs)])
      (conj cs (conj (if (or (not (conj-memp lhs ==?)) (conj-memp rhs ==?)) (disj lhs rhs) (disj rhs lhs)) ds))))

  ;; === QUANTIFICATION ===

  (define __ (vector '__)))
