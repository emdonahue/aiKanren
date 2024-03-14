;;TODO first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable
;;TODO consider a way to give matcho a global identity (maybe baking it into a defrel form?) so that matcho constraints with the same payload can simplify one another. eg, calling absento with the same payload on subparts of the same list many times
(library (matcho) ; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables"
                                        
  (export matcho matcho-pair
          expand-matcho matcho-attributed?; normalize-matcho matcho-attributed? matcho-test-eq?
          )
  (import (chezscheme) (datatypes) (mini-substitution) (state) (utils)) ;(streams) (variables) (goals)


  (define (expand-matcho g s p)
    ;; Runs the matcho goal with whatever ground variables have already been provided, assuming the remaining variables are unbound.
    ((matcho-goal g) s p (matcho-in-vars g)))

  (define (matcho-attributed? g var)
    (memq var (matcho-out-vars g)))
#;
  (define (matcho-test-eq? g out in) ; Shorthand for checking the comparable properties of matcho during unit testing.
    (and (matcho? g) (equal? (matcho-out-vars g) out) (equal? (matcho-in-vars g) in)))
  #;
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


