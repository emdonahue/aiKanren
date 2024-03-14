;TODO delete datatypes.ss and break it into smaller libs
(library (datatypes)
  (export expand-disjunctions search-strategy search-strategy/interleaving search-strategy/dfs max-depth answer-type answer-type/reified answer-type/state
          make-lazy-run lazy-run? lazy-run-stream lazy-run-query lazy-run-package set-lazy-run-stream
          package? empty-package
          fresh-vars vars->list
          stream?
          failure failure?
          var make-var var? var-id set-var-id!
          make-suspended suspended suspended? suspended-goal suspended-state
          make-mplus mplus? mplus-lhs mplus-rhs
          make-state+stream state+stream? state+stream-state state+stream-stream
          maybe-state?
          empty-state state? state-substitution state-varid set-state-substitution set-state-varid increment-varid instantiate-var set-state-datum state-datum
          empty-substitution
          make-constraint constraint? constraint-goal  proxy proxy? proxy-var constraint
          goal? goal-memp
          succeed fail succeed? fail?
          fresh exist conde
          make-== == ==? ==-lhs ==-rhs
          make-exist exist? exist-procedure suspend suspend? suspend-goal
          dfs-goal dfs-goal? dfs-goal-procedure
          make-conj conj conj?  conj-lhs conj-rhs conj* conj-memp conj-fold conj-filter conj-diff conj-member conj-memq conj-intersect conj-partition ;TODO replace conj-car/cdr with lhs/rhs
          make-disj disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs disj-succeeds? disj-factorize disj-factorized
          conde-disj conde? conde-lhs conde-rhs conde-car conde-cdr conde->disj
          pconstraint? pconstraint pconstraint-vars pconstraint-data pconstraint-procedure pconstraint-rebind-var pconstraint-check pconstraint-attributed?
          make-matcho matcho? matcho-out-vars matcho-in-vars matcho-goal expand-matcho normalize-matcho matcho-attributed? matcho-test-eq? simplify-matcho
          make-noto noto? noto-goal
          __)
  (import (chezscheme) (sbral) (variables) (goals) (streams) (utils))

  ;; === SUBSTITUTION ===

  

  



  



  
  ;; === RUNTIME PARAMETERS ===
  (define search-strategy/interleaving 'interleaving)
  (define search-strategy/dfs 'dfs)
  (define search-strategy ; Specifies the search strategy used by run. May be 'interleaving or 'dfs.
    ; Default: 'interleaving.
    (make-parameter search-strategy/interleaving
                    (lambda (s)
                      (unless (or (eq? s search-strategy/interleaving) (eq? s search-strategy/dfs))
                        (assertion-violation 'answer-type "Unrecognized search-strategy" s))
                      s)))
  
  (define expand-disjunctions (make-parameter #f)) ;TODO implement expand disjunction constraints in reifier. eg turn a bool constraint into a stream of t f.
  
  (define max-depth ; Specifies the maximum search, beyond which the search branch will automatically terminate. Depth corresponds to the number of allocated fresh variables in the substitution. This parameter applies to all search types, including interleaving.
    ; Default: (most-positive-fixnum).
    (make-parameter (most-positive-fixnum)
                    (lambda (d) (unless (integer? d) (assertion-violation 'max-depth "max-depth must be an integer" d)) d)))

  (define answer-type/reified 'reified)
  (define answer-type/state 'state)
  (define answer-type ; Defines the type of answers returned by run. May be 'reified for reified query variables or 'state for the entire internal state representation.
    ; Default: 'reified
    (make-parameter answer-type/reified
                    (lambda (t)
                      (unless (or (eq? t answer-type/reified) (eq? t answer-type/state))
                        (assertion-violation 'answer-type "Unrecognized answer-type" t))
                      t)))
  
  ;; === RUNNER ===
  (define-structure (lazy-run stream query package))
  
  (define (set-lazy-run-stream r s)
    (cert (lazy-run? r) (not (lazy-run? s)))
    (let ([r (vector-copy r)])
      (set-lazy-run-stream! r s) r))

  ;; === PACKAGE ===  
  (define-structure (package tables))
  (define empty-package (make-package '()))
  
  ;; === VAR ===
  

  (define-syntax fresh-vars ; Accepts a state and syntactic list of variables. Binds a new state with appropriately advanced variable id counter and runs the body forms in the scope of variables bound to the new logic variables.
    (syntax-rules ()
      [(_ [(end-state end-goal) (start-state (start-goal ...) ())] body ...)
       (let ([end-state start-state]
             [end-goal (conj* start-goal ...)])
         body ...)]
      [(_ [(end-state end-goal) (start-state (start-goal ...) (q ...))] body ...)
       (let* ([vid (state-varid start-state)]
              [q (begin (set! vid (fx1+ vid)) (make-var vid))] ...
              [end-goal (conj* start-goal ...)]
              [end-state (if (succeed? end-goal) start-state (set-state-varid start-state vid))])
         body ...)]
      [(_ [(end-state end-goal) (start-state (start-goal ...) q)] body ...)
       (fresh-vars [(end-state end-goal) (start-state (start-goal ...) (q))] body ...)]))

  (define-syntax vars->list ; Turns a syntactic list of variables into a reified Scheme list.
    (syntax-rules ()
      [(_ ()) '()]
      [(_ (q ...)) (list q ...)]
      [(_ q) q]))

  ;; === CONSTRAINT STORE ===  


  (define-syntax constraint ; Wrapped goals are conjoined and interpreted as a constraint.
    (syntax-rules ()
                                        ;TODO try applying constraint immediately when applied
      [(_ g ...) (let ([c (conj* g ...)]) (if (or (fail? c) (succeed? c)) c (make-constraint c)))]))
  


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
    ((pconstraint-procedure p) var val succeed succeed p))

  (define (pconstraint-attributed? p var)
    (memq var (pconstraint-vars p)))

  

  
  
  ;; === STATE ===
  

  

  

  ;; === STREAMS ===
  
  
  (define-structure (mplus lhs rhs))
  (define-structure (suspended goal state))
  (define (suspended g s s^)
    (cert (goal? g) (state? s))
    (exclusive-cond
     [(fail? g) failure]
     [(succeed? g) s]     
     [else (make-suspended g s^)]))
  (define-structure (state+stream state stream))

  (define (stream? s)
    (or (failure? s) (mplus? s) (suspended? s) (state? s) (state+stream? s)))
  
  ;; === GOALS ===
  
  (define (suspend g)
    (cert (goal? g))
    (if (or (succeed? g) (fail? g)) g (make-suspend g)))

  
    
  (define-syntax exist ; Equivalent to fresh, but does not suspend search. Only creates fresh variables.
    (syntax-rules ()
      [(_ q g ...)
       (lambda (start-state p c)
         (fresh-vars [(end-state end-goal) (start-state (g ...) q)] ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
                           (values end-goal end-state p c)))]))

  (define-syntax fresh ; Introduce fresh variables.
    ;; (fresh (x y z) ...)
    ;; Can be run with an empty variable list to simply suspend the search at that point.
    (syntax-rules ()
      [(_ q g ...)
       (exist q (suspend (conj* g ...)))]))

  (define-syntax conde ; Nondeterministic branching.
    (syntax-rules () 
      [(_ (g ...)) (conj* g ...)] ;TODO make conde do fail checks syntactically
      [(_ c0 c ...)
       (conde-disj (conde c0) (conde c ...))]))
  
  
  
  (define (normalize-matcho out in proc) ;TODO see if normalize-matcho adds anything to solve-matcho
    (cert (not (and (null? out) (null? in))))
    (exclusive-cond
     [(null? out)
      (let-values ([(_ g s p) (proc empty-state empty-package in)]) g)]
     [(var? (car out)) (make-matcho out in proc)]
     [else (if (pair? (car out)) (normalize-matcho (cdr out) (cons (car out) in) proc) fail)]))

  (define (expand-matcho g s p)
    ;; Runs the matcho goal with whatever ground variables have already been provided, assuming the remaining variables are unbound.
    ((matcho-goal g) s p (matcho-in-vars g)))

  (define (simplify-matcho g)
    (if (and (matcho? g) (null? (matcho-out-vars g)))
        (let-values ([(_ g s p) (expand-matcho g empty-state empty-package)]) g)
        g))

  (define (matcho-attributed? g var)
    (memq var (matcho-out-vars g)))

  (define (matcho-test-eq? g out in) ; Shorthand for checking the comparable properties of matcho during unit testing.
    (and (matcho? g) (equal? (matcho-out-vars g) out) (equal? (matcho-in-vars g) in)))
  

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

  
  
  ;; CONJ
  

  ;; DISJ
  

  ;; === QUANTIFICATION ===

  )
