;;TODO first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable
;;TODO consider a way to give matcho a global identity (maybe baking it into a defrel form?) so that matcho constraints with the same payload can simplify one another. eg, calling absento with the same payload on subparts of the same list many times
(library (matcho) ; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables"

  (export matcho matcho-pair
          matcho3 matcho-tst matcho5 matcho9 matcho/fresh2 pattern->term2 matcho6 matcho11 matcho/fresh pattern->term ;matcho5 matcho4
          expand-matcho matcho-attributed? matcho-attributed? matcho-test-eq?)
  (import (chezscheme) (streams) (variables) (goals) (mini-substitution) (state) (utils))

  #;
  (define-syntax unroll-lst
    (syntax-rules ()
  [(_ a)]))

  #;
  (comment
   (let ([in-var (extract-in-vars pattern)])
     (let ([s (mini-unify (pattern->term pattern) (list out ...))])
       (let ([in-var (walk in-var s)] ...)
         (if (no-fresh (list in-var ...))
             (begin body ...)
  (make-matcho ))))))


  (define-syntax matcho11
    (syntax-rules ()
      [(_ (bindings ...) body ...) (matcho11 match (bindings ...) body ...)]
      [(_ name (bindings ...) body ...)
       (matcho12 name (bindings ...) (body ...))]))

  (define-syntax matcho12
    (syntax-rules ()
      [(_ name ([pattern expr] ...) (body ...))
       (matcho/fresh3 (pattern ...)
                      (begin
                        (matcho/ground [pattern expr] ...)
                        (conj* body ...)))]))

  (define-syntax matcho/ground
    (syntax-rules ()
      [(_ [(p-car . p-cdr) expr])
       (not (eq? (syntax->datum #'p-car) 'quote))
       (when (pair? expr) (matcho/ground [p-car (car expr)]) (matcho/ground [p-cdr (cdr expr)]))]
      
      [(_ [pattern expr])
       (identifier? #'pattern)
       (set! pattern expr)]

      [(_ [pattern expr]) (void)]
      
      [(_  binding0 binding ...)
       (begin (matcho/ground binding0) (matcho/ground binding ...))]))

  (define-syntax matcho/fresh3
    ;; Called when matcho runs as a goal to instantiate any fresh variables in the patterns and bind them in the lexical environment.
    (syntax-rules ()
      [(_ bindings body) (matcho/fresh3 bindings body ())] ; When initially called, create an empty list of duplicate ids.
      
      [(_ () body dup-ids) body ] ; When out of patterns, all vars are bound, so simply execute body.
      
      [(_ ((p-car . p-cdr) pattern ...) body dup-ids) ; Destructure pair patterns and push identifiers into pattern buffer.
       (not (eq? (syntax->datum #'p-car) 'quote))
       (matcho/fresh3 (p-car p-cdr pattern ...) body dup-ids)]
      
      [(_ (p0 p ...) body (dup-id ...)) ; Create a fresh var if we see an identifier we haven't seen before & bind it.
       (and (identifier? #'p0) (not (memp (lambda (i) (bound-identifier=? i #'p0)) #'(dup-id ...))))
       (let ([p0 (make-var 0)])         
         (matcho/fresh3 (p ...) body (p0 dup-id ...)))]

      [(_ (p0 p ...) body dup-ids) ; Ignore anything not a new identifier.
       (matcho/fresh (p ...) body dup-ids)]))

  (define matcho-tst
   (syntax-rules ()
     [(_ a) (list a)]
))

  (define-syntax matcho-ctn
    (syntax-rules ()
      [(_ body ...) (matcho7 body ...)]))

  (define-syntax matcho9
    (syntax-rules ()
      [(_ (bindings ...) body ...) (matcho9 match (bindings ...) body ...)]
      [(_ name ([p v] ...) body ...)
       (let-values ([(expanded? c m) (matcho2 name () () #f ([v p] ...) body ...)])
         (conj c m))]))
  
  (define-syntax matcho3
    (syntax-rules ()
      [(_ (bindings ...) body ...) (matcho3 match (bindings ...) body ...)]
      [(_ name (bindings ...) body ...)
       (let-values ([(expanded? c m) (matcho2 name () () #f (bindings ...) body ...)])
         (conj c m))]))

  ;; constraint situation:
  ;; the ground list will be full, but it may contain free vars that match sub patterns, so we should expect to destructure all the input terms (possibly failing) and then be left with a sub problem of more bindings that may require that we return a new suspended matcho. this is fundamentally a similar problem to

  #;
  (or (not (identifier? #'out))
           (not (memp (lambda (v)
                        (display v)
                        (display #'out)
                        (and (identifier? v) (bound-identifier=? #'out! v))) (filter identifier? #'(suspended-var ...))))
           (assertion-violation 'matcho "Dup binding" 'test))

  (define-syntax matcho-c
    (syntax-rules ()
      [(_ shared-ids ([out (p-car . p-cdr)]) (no-match ...) var ground body ...)
       (matcho2 shared-ids (no-match ...) #t ([ground (p-car . p-cdr)]) body ...)]

      [(_ shared-ids ([out (p-car . p-cdr)] binding ...) (no-match ...) var ground body ...)
       (if (eq? out var)
           (matcho2 shared-ids (no-match ... binding ...) #t ([ground (p-car . p-cdr)]) body ...)
           (matcho-c shared-ids (binding ...) ([out (p-car . p-cdr)] no-match ...) var ground body ...))]))

  (define-syntax matcho/match-one
    ;; Called when constraints are fired from the store. Guarantees that at least one variable is now ground (and is a pair, since non-pair ground terms fail early in the solver). Without this, we would need to generate an infinite tree of cases for each possible variable-variable substitution. By handling that part at runtime, we can just generate the tree of ever smaller lists of variables that bottom out and terminate.
    (syntax-rules ()

      [(_ name shared-ids ([out p] ...) () body ...)
       (assertion-violation 'matcho "Matcho constraint must contain at least one ground pair" (list out ...))]

      [(_ name shared-ids (suspended-binding ...) ([out (p-car . p-cdr)] binding ...) body ...)
       (if (pair? out) ; When we find the pair, destructure it and set the usual match procedure running.
           (matcho2 name shared-ids () #f
                    ([(car out) p-car] [(cdr out) p-cdr] suspended-binding ... binding ...) body ...)
           ;; For variables, set them aside until we find the pair then dump them all back in and let the usual matcho handle it.
           (matcho/match-one name shared-ids (suspended-binding ... [out (p-car . p-cdr)]) (binding ...) body ...))]))

  (define-syntax matcho/fresh
    ;; Called when matcho runs as a goal to instantiate any fresh variables in the patterns and bind them in the lexical environment.
    (syntax-rules ()
      [(_ vid shared-ids () body ...) (begin body ...) ] ; When out of patterns, all vars are bound, so simply execute body.
      
      [(_ vid shared-ids ((p-car . p-cdr) pattern ...) body ...) ; Destructure pair patterns and push identifiers into pattern buffer.
       (not (eq? (syntax->datum #'p-car) 'quote))
       (matcho/fresh vid shared-ids (p-car p-cdr pattern ...) body ...)]
      
      [(_ vid (shared-id ...) (p0 p ...) body ...) ; Create a fresh var if we see an identifier we haven't seen before & bind it.
       (and (identifier? #'p0) (not (memp (lambda (i) (bound-identifier=? i #'p0)) #'(shared-id ...))))
       (let ([vid (fx1+ vid)])
         (let ([p0 (make-var vid)])         
          (matcho/fresh vid (p0 shared-id ...) (p ...) body ...)))]

      [(_ vid shared-ids (p0 p ...) body ...) ; Ignore anything not a new identifier.
       (matcho/fresh vid shared-ids (p ...) body ...)]))

  (define-syntax pattern->term
    (syntax-rules ()
      [(_ ()) '()]
      [(_ (a . d))
       (not (eq? (syntax->datum #'a) 'quote))
       (cons (pattern->term a) (pattern->term d))]
      [(_ a) a]))

  (meta define (syntax->pair p)
    (syntax-case p ()
      [() '()]
      [(a . d) (cons (syntax->pair #'a) (syntax->pair #'d))]
      [a #'a]))
  
  (meta define (matcho/contains-free-name pattern shared-ids)
        (if (pair? pattern)
            (or (matcho/contains-free-name (car pattern) shared-ids)
                (matcho/contains-free-name (cdr pattern) shared-ids))
            (and (identifier? pattern)
                 (not (memp (lambda (i) (bound-identifier=? i pattern)) shared-ids))))
        )
  
  (define-syntax matcho2 ;TODO have the new name binder re-introduce the suspended bindings to check if any are now fully ground
    ;; TODO test if goal continues to walk vars pulled up by walking previous vars into pairs
    (syntax-rules ()
      [(_ name shared-ids () is-constraint? () body ...) (values #t succeed (conj* body ...))] ; No-op. Once all bindings have been processed, run the body.

      [(_ name shared-ids ([out (p-car . p-cdr)] ...) #f () body ...) ; Suspend free vars as a goal.
       (values #f succeed
               (make-matcho4 (list out ...)
                             (let ([name
                                    (case-lambda
                                      [(s out ...)
                                       (let-values ([(maybe-s ==s g) ;TODO swap walk var with walk binding, check constraint for possible failure, and if not continue as normal with var
                                                     (matcho2 name shared-ids () s ([(walk-var s out) (p-car . p-cdr)] ...) body ...)])
                                         (if (state? maybe-s) ; If the state has been modified, it will be returned as maybe-s. Otherwise, #t signifying no change to state, so we can reuse the old state.
                                             (values (conj ==s g) maybe-s)
                                             (values (conj ==s g) s)))]
                                      [(out ...)
                                       (matcho/match-one name shared-ids () ([out (p-car . p-cdr)] ...) body ...)])]) name)))]

      [(_ name shared-ids ([var pattern] ...) s () body ...) ; Create fresh vars.
       (let ([vid (state-varid s)])
         (matcho/fresh
          vid shared-ids (pattern ...)          
          (values (set-state-varid s vid) (conj* (== var (pattern->term pattern)) ...) (conj* body ...))))]

      [(_ name shared-ids suspended-bindings is-constraint? ([out! ()] binding ...) body ...) ; Empty lists quote the empty list and recurse as ground.
       (matcho2 name shared-ids suspended-bindings is-constraint? ([out! '()] binding ...) body ...)]

      [(_ name (shared-id ...) (suspended-binding ...) is-constraint? ([out! p] binding ...) body ...) ; New identifier
       (and (identifier? #'p) (not (memp (lambda (i) (bound-identifier=? i #'p)) #'(shared-id ...))))
       (let ([p out!]) ; Create a let binding and add the name to our shared-id list to check for future re-uses of the same name in the match pattern.
         (matcho2 name (p shared-id ...) () is-constraint? (suspended-binding ... binding ...) body ...))]

      #;
      [(_ name (shared-id ...) suspended-bindings is-constraint? ([out! p] binding ...) body ...) ; Shared identifier
       (and (identifier? #'p) (memp (lambda (i) (bound-identifier=? i #'p)) #'(shared-id ...)))
       (let ([out out!])
         (let ([u (== p out)]) ; Unify with the empty list to handle the tails of list patterns.
           (if (fail? u) (values #t fail fail)
               (let-values ([(expanded? c m) (matcho2 name (shared-id ...) suspended-bindings is-constraint? (binding ...) body ...)])
                 (values expanded? (conj u c) m)))))]

      [(_ name (shared-id ...) (suspended-binding ...) is-constraint? ([out! (p-car . p-cdr)] binding ...) body ...) ; Pair
       (and (not (eq? (syntax->datum #'p-car) 'quote)) (matcho/contains-free-name (syntax->pair #'(p-car . p-cdr)) #'(shared-id ...)))
       (let ([out out!])
         (exclusive-cond
          [(pair? out) ; Destructure ground pairs and pass their sub-parts to the matcher.
           (matcho2 name (shared-id ...) (suspended-binding ...) is-constraint?
                    ([(car out) p-car] [(cdr out) p-cdr] binding ...) body ...)]
          [(var? out) ; Set aside variable matchers to wrap in the suspended goal at the end.
           (matcho2 name (shared-id ...) (suspended-binding ... [out (p-car . p-cdr)]) is-constraint? (binding ...) body ...)]
          [else (values #t fail fail)]))]

      [(_ name shared-ids suspended-bindings is-constraint? ([out! ground] binding ...) body ...) ; Ground. Matching against ground primitives simplifies to unification.
       (let ([g (== out! (pattern->term ground))])
         (if (fail? g) (values #t fail fail)
             (let-values ([(expanded? c m) (matcho2 name shared-ids suspended-bindings is-constraint? (binding ...) body ...)])
               (values expanded? (conj g c) m))))]))


  (define matcho6
    (syntax-rules ()
      [(_ (bindings ...) body ...)
       (matcho5 () () #f (bindings ...) body ...)]))
#;
  (define matcho6
    (syntax-rules ()
      [(_ (bindings ...) body ...)
       (let-values ([(c m) (matcho5 () () #f (bindings ...) body ...)])
         (conj c m))]))
  (define matcho/fresh2
    ;; Called when matcho runs as a goal to instantiate any fresh variables in the patterns and bind them in the lexical environment.
    (syntax-rules ()
      [(_ vid shared-ids () body ...) (begin body ...) ] ; When out of patterns, all vars are bound, so simply execute body.
      
      [(_ vid shared-ids ((p-car . p-cdr) pattern ...) body ...) ; Destructure pair patterns and push identifiers into pattern buffer.
       (not (eq? (syntax->datum #'p-car) 'quote))
       (matcho/fresh2 vid shared-ids (p-car p-cdr pattern ...) body ...)]
      
      [(_ vid (shared-id ...) (p0 p ...) body ...) ; Create a fresh var if we see an identifier we haven't seen before & bind it.
       (and (identifier? #'p0)
            (not (memp (lambda (i) (bound-identifier=? i #'p0)) #'(shared-id ...)))
            )
       (let ([p0 (make-var vid)])
         (set! vid (fx1+ vid))
         (matcho/fresh2 vid (p0 shared-id ...) (p ...) body ...))]

      [(_ vid shared-ids (p0 p ...) body ...) ; Ignore anything not a new identifier.
       (matcho/fresh2 vid shared-ids (p ...) body ...)]))

  (define pattern->term2
    (syntax-rules ()
      [(_ ()) '()]
      [(_ (a . d))
       (not (eq? (syntax->datum #'a) 'quote))
       (cons (pattern->term2 a) (pattern->term2 d))]
      [(_ a) a]))
  
  (define matcho5
    (syntax-rules ()
      [(_ shared-ids () is-constraint? () body ...) (values #t succeed (conj* body ...))] ; No-op. Once all bindings have been processed, run the body.

      [(_ shared-ids ([out (p-car . p-cdr)] ...) #f () body ...) ; Suspend free vars as a goal.
       (values #f succeed
               (make-matcho4 (list out ...)
                             (case-lambda
                               [(s out ...)
                                (let-values ([(maybe-s ==s g)
                                              (matcho5 shared-ids () s ([(walk-var s out) (p-car . p-cdr)] ...) body ...)])
                                  (if (state? maybe-s) ; If the state has been modified, it will be returned as maybe-s. Otherwise, #t signifying no change to state, so we can reuse the old state.
                                      (values (conj ==s g) maybe-s)
                                      (values (conj ==s g) s)))]
                               [(out ...)
                                (matcho/match-one shared-ids () ([out (p-car . p-cdr)] ...) body ...)])))]

      [(_ shared-ids ([var pattern] ...) s () body ...) ; Create fresh vars.
       (let ([vid (state-varid s)])
         (matcho/fresh2
          vid shared-ids (pattern ...)
          (begin
            ;(display 'shared-ids)
            (values s succeed succeed))
          #;
          (values (set-state-varid s vid) (conj* (== var (pattern->term2 pattern)) ...) (conj* body ...))))]

      [(_ shared-ids suspended-bindings is-constraint? ([out! ()] binding ...) body ...) ; Empty lists quote the empty list and recurse as ground.
       (matcho5 shared-ids suspended-bindings is-constraint? ([out! '()] binding ...) body ...)]

      [(_ (shared-id ...) suspended-bindings is-constraint? ([out! name] binding ...) body ...) ; New identifier
       (and (identifier? #'name) (not (memp (lambda (i) (bound-identifier=? i #'name)) #'(shared-id ...))))
       (let ([name out!]) ; Create a let binding and add the name to our shared-id list to check for future re-uses of the same name in the match pattern.
         (matcho5 (name shared-id ...) suspended-bindings is-constraint? (binding ...) body ...))]

      [(_ (shared-id ...) suspended-bindings is-constraint? ([out! name] binding ...) body ...) ; Shared identifier
       (and (identifier? #'name) (memp (lambda (i) (bound-identifier=? i #'name)) #'(shared-id ...)))
       (let ([out out!])
         (let ([u (== name out)]) ; Unify with the empty list to handle the tails of list patterns.
           (if (fail? u) (values #t fail fail)
               (let ([name out])
                 (let-values ([(expanded? c m) (matcho5 (name shared-id ...) suspended-bindings is-constraint? (binding ...) body ...)])
                   (values expanded? (conj u c) m))))))]

      [(_ shared-ids (suspended-binding ...) is-constraint? ([out! (p-car . p-cdr)] binding ...) body ...) ; Pair
       (not (eq? (syntax->datum #'p-car) 'quote))
       (let ([out out!])
         (exclusive-cond
          [(pair? out) ; Destructure ground pairs and pass their sub-parts to the matcher.
           (matcho5 shared-ids (suspended-binding ...) is-constraint?
                    ([(car out) p-car] [(cdr out) p-cdr] binding ...) body ...)]
          [(var? out) ; Set aside variable matchers to wrap in the suspended goal at the end.
           (matcho5 shared-ids (suspended-binding ... [out (p-car . p-cdr)]) is-constraint? (binding ...) body ...)]
          [else (values #t fail fail)]))]

      [(_ shared-ids suspended-bindings is-constraint? ([out! ground] binding ...) body ...) ; Ground. Matching against ground primitives simplifies to unification.
       (let ([g (== out! ground)])
         (if (fail? g) (values #t fail fail)
             (let-values ([(expanded? c m) (matcho5 shared-ids suspended-bindings is-constraint? (binding ...) body ...)])
               (values expanded? (conj g c) m))))]))





  (define (expand-matcho g s p)
    ;; Runs the matcho goal with whatever ground variables have already been provided, assuming the remaining variables are unbound.
    ((matcho-goal g) s p (matcho-in-vars g)))

  (define (matcho-attributed? g var)
    (memq var (matcho-out-vars g)))

  (define (matcho-test-eq? g out in) ; Shorthand for checking the comparable properties of matcho during unit testing.
    (and (matcho? g) (equal? (matcho-out-vars g) out) (equal? (matcho-in-vars g) in)))

  (define (normalize-matcho out in proc) ;TODO see if normalize-matcho adds anything to solve-matcho
    (cert (not (and (null? out) (null? in))))
    (exclusive-cond
     [(null? out)
      (let-values ([(_ g s p) (proc empty-state empty-package in)]) g)]
     [(var? (car out)) (make-matcho out in proc)]
     [else (if (pair? (car out)) (normalize-matcho (cdr out) (cons (car out) in) proc) fail)]))

  (define-syntax build-substitution
    ;; Walks each out-variable in turn and unifies it with its pattern, failing the entire computation if any pattern unification fails before walking subsequent variables.
    (syntax-rules ()
      [(_ state package substitution grounding ((out-var pattern)) body ...)
       (let* ([out-var (if (null? grounding) (walk-var state out-var) (car grounding))] ;TODO integrate constraint substitutions with matcho
              [grounding (if (null? grounding) grounding (cdr grounding))]
              [substitution (mini-unify substitution (build-pattern pattern) out-var)])
         (if (failure? substitution)
             (values #f fail failure package)
             (begin body ...)))]
      [(_ state package substitution grounding (binding bindings ...) body ...)
       (build-substitution state package substitution grounding (binding)
                           (build-substitution state package substitution grounding (bindings ...) body ...))]))

  (define-syntax build-pattern
    ;; Turn a pattern match schema into a full scheme object for unification.
    (syntax-rules (quote)
      [(_ (quote q)) 'q]
      [(_ (h . t)) (cons (build-pattern h) (build-pattern t))]
      [(_ ()) '()]
      [(_ v) v]))

  (define-syntax matcho-pair ;TODO generalize matcho-pair to multiple pairs, pairs with constant patterns, and other common patterns such as a-list
    ;; Optimization to inline the destructuring of a single generic pair.
    (syntax-rules () ;TODO specialize multiple pair matcho-pair on different modes (ground, free, etc) so we can always instantly destructure whatever is ground. may involve further manipulations of goal order based on mode
      [(_ ([out-var (p-car . p-cdr)]) body ...) ;TODO can we make a generalized matcho out of matcho-pair on each pair of a pattern?
       (exclusive-cond
        [(var? out-var)
         (make-matcho
          (list out-var)
          '()
          (lambda (state package grounding)
            (let ([out-var (if (null? grounding) (walk-var state out-var) (car grounding))])
              (exclusive-cond
               [(pair? out-var)
                (values #t
                        (let ([p-car (car out-var)]
                              [p-cdr (cdr out-var)])
                          (conj* body ...))
                        state package)]
               [(var? out-var)
                (values
                 #f
                 (let ([p-car (make-var (fx1+ (state-varid state)))]
                       [p-cdr (make-var (fx+ 2 (state-varid state)))])
                   (conj* (== out-var (cons p-car p-cdr)) body ...))
                 (if (var? out-var) (set-state-varid state (fx+ 2 (state-varid state))) state)
                 package)]
               [else (values #t fail failure package)]))))]
        [(pair? out-var) ; If the term is ground, just destructure it and continue.
         (let ([p-car (car out-var)]
               [p-cdr (cdr out-var)])
           (conj* body ...))]
        [else fail])]))

  (define-syntax (matcho bindings) ; A pattern-matching equivalent for fresh.
    ;; (matcho ([x (a . 1)] [y ('b . c)] ...) ...)
    ;; The above form destructures the input variables x and y, ensuring that (== (cdr x) 1) and (== (car y) 'b) and then binding a and c to the car and cdr of x and y respectively. a and b may then be accessed like normal let bindings within the scope of the wrapped goals.
    ;; In this implementation, the vast majority of fresh calls are better implemented as matcho calls. In addition to instantiating fresh variables and suspending the search as needed, matcho offers a convenient syntax for destructuring input terms---which is the most common use case for fresh---and performs various optimizations while doing so.

    ;; TODO specialize matcho for constraints vs goal & let interpreter decide implementation. constraint never needs to make fresh vars, goal doesn't need to know which vars are free (just whether)
    ;; TODO can we fire matcho immediately if its structural recursion instead of waiting on a conjunct ahead of it that may be all free? reordering conjuncts

    (define extract-vars
      ;; Extracts unique logic variable identifiers from the aggregate patterns.
      (case-lambda ;TODO if matcho out-vars do not appear in the body, is there is no need to apply occurs-check constraints?
        [(pattern) (extract-vars pattern '())]
        [(pattern vs)
         (if (pair? pattern) (extract-vars (car pattern) (extract-vars (cdr pattern) vs))
             (syntax-case pattern (quote)
               [(quote q) vs]
               [v (identifier? #'v)
                  (if (memp (lambda (e) (bound-identifier=? e #'v)) vs) vs (cons #'v vs))]
               [(h . t) (extract-vars #'h (extract-vars #'t vs))]
               [a vs]))]))

    (syntax-case bindings ()
      #;
      [(_ label ([out-var (p-car . p-cdr)]) body ...)
       (and (identifier? #'p-car) (identifier? #'p-cdr))
      #'(matcho-pair ([out-var (p-car . p-cdr)]) body ...)]
      #;
      [(_ ([out-var (p-car . p-cdr)]) body ...)
       (and (identifier? #'p-car) (identifier? #'p-cdr))
       #'(matcho-pair ([out-var (p-car . p-cdr)]) body ...)]
      [(_ ([out-var (p-car . p-cdr)] ...) body ...) ;TODO allow matcho to match non pairs to allow constructing pairs from ground terms, and then =/= simplify should not fail on pairs for matcho
       #'(matcho matcho ([out-var (p-car . p-cdr)] ...) body ...)]
      [(_ label ([out-var (p-car . p-cdr)] ...) body ...) ;TODO add fender to matcho to prevent duplicate lhs vars and cyclic pattern vars (since out-vars are bound beneath in-vars, so the shadowing will go the wrong way)
       (with-syntax ([(in-var ...) (extract-vars #'(p-car ... p-cdr ...))]) ; Get new identifiers from pattern bindings that may require fresh logic variables.
         #`(normalize-matcho
            (list out-var ...) ;TODO equip matcho with the patterns externally to fail constraints without invoking goal.
            '()
            (let ([label (lambda (state package grounding)
                           (let ([substitution '()]
                                 [grounding (reverse grounding)]
                                 [in-var (make-var 0)] ...) ; Create blank dummy variables for each identifier.
                             (build-substitution
                              state package substitution grounding
                              ((out-var (p-car . p-cdr)) ...) ; Unify each external destructured variable with its pattern in a new empty substitution.
                              (let ([in-var (mini-reify substitution in-var)] ...) ; Reify each fresh variable in the substitution to see if it is already bound by the pattern match with a ground term in the destructured external variable.
                                (values
                                 (and (not (var? out-var)) ...) ; If all out-var are ground/bound, consider this relation structurally recursive and keep expanding it in the goal interpreter. TODO under what conditions should matcho continue?
                                 (conj*
                                  (== out-var (mini-reify substitution out-var)) ... ; Generate unifications of each external variable with its reified pattern, which has extracted all possible ground information from both the external variable and the pattern itself due to the double reification.
                                  body ...)
                                 (set-state-varid ; Set as many variable ids as needed for fresh variables that remain fresh and so must enter the larger search as unbound variables.
                                  state (fold-left
                                         (lambda (id v)
                                           (if (and (var? v) (zero? (var-id v)))
                                               (begin (set-var-id! v (fx1+ id)) (fx1+ id)) id))
                                         (state-varid state) (list in-var ...)))
                                 package)))))]) label)))])))
