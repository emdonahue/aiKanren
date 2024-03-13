(library (goals) ; Definitions for core mk goals
  (export goal?
          make-== ==? ==-lhs ==-rhs ==
          succeed fail succeed? fail?
          make-noto noto? noto-goal
          make-conj conj? conj-lhs conj-rhs
          make-disj disj? disj-lhs disj-rhs
          make-exist exist? exist-procedure
          make-suspend suspend? suspend-goal
          make-matcho matcho? matcho-out-vars matcho-in-vars matcho-goal
          proxy proxy? proxy-var proxy
          conde? conde-lhs conde-rhs conde-car conde-cdr conde-disj
          pconstraint pconstraint? pconstraint-vars pconstraint-data pconstraint-procedure
          make-constraint constraint? constraint-goal
          dfs-goal dfs-goal? dfs-goal-procedure
          __)
  (import (chezscheme) (variables) (utils))

  ;; === TRIVIAL ===
  (define succeed ; A goal that trivially succeeds. Used as a constant rather than a function call.
    (vector 'succeed))
  (define fail ; A goal that trivially fails. Used as a constant rather than a function call.
    (vector 'fail))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

  ;; === == ===
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints. also break two pairs into a conj of ==. then we can simplify the order checking inside the unifier
  (define (== x y) ; Implements unification between terms.
    (cond
     [(or (eq? x __) (eq? y __)) succeed]
     [(equal? x y) succeed]
     [(var? x) (if (var? y) (if (var< x y) (make-== x y) (make-== y x)) (make-== x y))]
     [(var? y) (make-== y x)]
     [(and (pair? x) (pair? y)) (make-== x y)]
     [else fail]))

  ;; === DFS ===
  (define-structure (dfs-goal procedure))
  (define (dfs-goal p) ; Wraps a procedure that has the same signature as run-goal-dfs. Called internally by run-goal-dfs, which transparently passes its arguments to the procedure and returns the resulting values. Used to dynamically extend the behavior of the dfs interpreter.
    (cert (procedure? p))
    (make-dfs-goal p))

  ;; === PROXY ===
  (define-structure (proxy var)) ;TODO make proxies remove only their specific constraint and return other conjoined constraints to the store, not rerun all conjuncts.
  (define (proxy v) ; If a constraint is bound to multiple variables, we only keep one true copy of the constraint. The other variables receive proxy constraints that remember the one variable with the true constraint. When solving, proxy constraints fetch the true constraint and run that to avoid running multiple copies of the same constraint. In addition to being generally inefficient, multiple copies can lead to various kinds of blow up conditions depending on how solving is implemented (eg multiple copies of a fresh will yield constraints with different object identities, which may make it hard to do any simplification, especially if we simplify them locally first).
    (cert (var? v))
    (make-proxy v))

  ;; === CONDE ===
  (define-structure (conde lhs rhs))
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

  ;; === PCONSTRAINT ===
  (define-structure (pconstraint vars procedure data))
  (define (pconstraint vars procedure data)
    (cert (list? vars) (procedure? procedure))
    (make-pconstraint vars procedure data))

  ;; === CONSTRAINT ===
  (define-structure (constraint goal))

  ;; === QUANTIFICATION ===
  (define __ ; Wildcard logic variable that unifies with everything without changing substitution.
    (vector '__))

  ;; === OTHER GOALS ===
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  (define-structure (noto goal)) ; Negated goal
  (define-structure (exist procedure))
  (define-structure (suspend goal))
  (define-structure (matcho out-vars in-vars goal))
  
  ;; === CONTRACTS ===
  (define (goal? g)
    (or (matcho? g) (procedure? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g) (pconstraint? g) (conde? g) (exist? g) (suspend? g) (proxy? g) (dfs-goal? g))))
