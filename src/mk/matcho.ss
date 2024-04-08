;;TODO first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable
;;TODO consider a way to give matcho a global identity (maybe baking it into a defrel form?) so that matcho constraints with the same payload can simplify one another. eg, calling absento with the same payload on subparts of the same list many times
(library (matcho) ; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables"

  (export matcho/expand matcho-attributed-vars matcho/run
          matcho11 pattern->term)
  (import (chezscheme) (streams) (variables) (goals) (mini-substitution) (state) (utils))

  ;; TODO make matcho work for pure values outside of mk. a la carte unification/pattern matching
  ;; TODO make a special pre-sequence to bind the pure single var renames with no pair patterns
  ;; TODO can we fail to fail if matcho is waiting un a binding that is partially filled and that has constraints that would make it fail even in its partial state?
  ;; TODO do we need expanded? for constraints?
  ;; TODO return old state if we expand inner goal and it trivially succeeds
  ;; TODO replace not pairo in absento with not matcho on a pair, which will preverve fresh id bc of trivial succeed
  ;; TODO consider else clause for returning a new goal if matcho fails the pattern match
  ;; TODO consider a cond form that nests matcho else clauses to create a cond like form without lots of negation

  (define (pattern-var? v)
    (cert (var? v))
    (zero? (var-id v)))

  (define (pattern-binding? b)
    (cert (pair? b) (var? (car b)))
    (pattern-var? (car b)))

  (define (matcho-attributed-vars g)
    (cert (matcho14? g))
    (map car (remp pattern-binding? (matcho14-substitution g))))

  (define (matcho/run g s)
    (cert (matcho14? g) (state? s))
    (let-values ([(expanded? g ==s) (matcho/expand g s)])
      (if expanded? ;TODO try returning expanded and not suspending if true
          (values (conj ==s g) s)
          (let* ([vid (state-varid s)]
                 [pattern-bindings (map (lambda (b) (set! vid (fx1+ vid)) (cons b (make-var vid)))
                                        (substitution-pattern-vars (matcho14-substitution g)))]
                 [sub/ground (map (lambda (b) ;TODO can pattern vars be rhs to both pattern and attributed or just one?
                                     (cons (car b) ; TODO instead of walking/replacing the rhs pattern vars, just stick them on the front and use reify. may b able to save time by only reifynig pattern vars, since attr vars wont be lhs
                                           (fresh-patterns (cdr b) pattern-bindings))) (matcho14-substitution g))])
            (let-values ([(sub/pattern sub/attributed) (partition pattern-binding? sub/ground)])
              (values (conj* ==s (substitution->unification sub/attributed) ((matcho14-ctn g) (append pattern-bindings sub/pattern))) (set-state-varid s vid)))))))

  (define matcho/make-fresh
    (case-lambda
      [(s vid) (matcho/make-fresh s vid s)]
      [(s vid s/fresh)
       (if (null? s) (values s/fresh vid)
           (let-values ([(s/fresh vid) (matcho/make-fresh/binding (cdar s) vid s/fresh)])
             (matcho/make-fresh (cdr s) vid s/fresh)))]))

  (define (substitution->unification sub)
    (fold-left (lambda (c b) (conj (== (car b) (cdr b)) c)) succeed sub))
  
  (define (fresh-patterns b vs)
    (exclusive-cond
     [(pair? b) (cons (fresh-patterns (car b) vs) (fresh-patterns (cdr b) vs))]
     [(and (var? b) (pattern-var? b)) (cdr (assq b vs))]
     [else b]))

  (define (matcho/make-fresh/binding b vid s)
    (exclusive-cond
     [(pair? b) (let-values ([(vid s) (matcho/make-fresh/binding (car b) vid s)])
                  (matcho/make-fresh/binding (cdr b) vid s))]
     [(and (var? b) (pattern-var? b) (not (assq b s)))
      (let ([vid (fx1+ vid)]) (values ))]))
  
  (define substitution-pattern-vars
    (case-lambda
      [(s) (fold-left
            (lambda (vs b) (substitution-pattern-vars (cdr b) vs)) '() s)]
      [(b vs)
       (exclusive-cond
        [(pair? b) (substitution-pattern-vars (cdr b) (substitution-pattern-vars (car b) vs))]
        [(and (var? b) (pattern-var? b) (not (memq b vs))) (cons b vs)]
        [else vs])]))
  
  (define matcho/expand
    (org-case-lambda matcho/expand
      [(g s) (matcho/expand g s (matcho14-substitution g) succeed '())]
      [(g s sub ==s vs)
       (cert (matcho14? g) (state? s) (list? sub) (goal? ==s) (list? vs))
       (let ([free-binding (find (lambda (b) (and (not (zero? (var-id (car b)))) ; Get an unwalked attributed var
                                                  (not (memq (car b) vs))
                                                  (not (no-pattern-vars? (cdr b))))) sub)])
         (if free-binding ; If one exists,
             (let ([sub (mini-unify (remq free-binding sub) ; walk the var and unify its value into the mini substitution.
                                    (cdr free-binding)  (walk-var s (car free-binding)))])
               (if (failure? sub) (values #t fail fail) ; If that unification doesn't fail,
                   (let ([sub ; reify the entire mini substitution so that fully ground attributed vars can be identified by inspection.
                          (map (lambda (b) (cons (car b) (mini-reify sub (cdr b)))) sub)]) ; TODO we may only need to reify attr vars
                     (let-values ([(sub/ground sub/free) ; Extract ground attributed variables as unifications by inspection of reified rhs.
                                       (partition (lambda (b) (and (not (zero? (var-id (car b))))
                                                                   (no-pattern-vars? (cdr b)))) sub)])
                      (if (for-all (lambda (b) (zero? (var-id (car b)))) sub/free) ; If there are no more attributed vars, we can never add new information, so we must have all the ground information and we can expand the body.
                          (values #t ((matcho14-ctn g) sub/free) (conj
                                                                  (fold-left (lambda (c b) (conj (== (car b) (cdr b)) c)) ==s sub/ground) ==s)) ; Therefore execute the body.
                          (matcho/expand g s sub/free ; and continue walking unwalked variables.
                                         (fold-left (lambda (c b) (conj (== (car b) (cdr b)) c)) ==s sub/ground)
                                         (cons (car free-binding) vs)))))))
             ;; If there are no unwalked attributed vars remaining, suspend expansion and return.
             (values #f (make-matcho14 sub (matcho14-ctn g)) ==s)))]))


  
  (define (no-pattern-vars? x)
    (if (pair? x)
        (and (no-pattern-vars? (car x)) (no-pattern-vars? (cdr x)))
        (not (and (var? x) (zero? (var-id x))))))

  (define (pattern-vars? x)
    (if (pair? x)
        (or (pattern-vars? (car x)) (pattern-vars? (cdr x)))
        (and (var? x) (zero? (var-id x)))))

  (define (reify-substitution2 s)
    (map (lambda (b) (cons (car b) (mini-reify s (cdr b)))) s))

  (define reify-substitution
    (case-lambda
      [(s) (reify-substitution s s succeed '() #t)]
      [(s s-full ==s s-out fully-ground?)
       (if (null? s) (values s-out ==s fully-ground?)
           (let ([lhs (caar s)])
             (if (pattern-var? lhs) ; Pattern vars must remain until the end to let us perform final look up bindings, so skip.
                 (reify-substitution (cdr s) s-full ==s (cons (car s) s-out) fully-ground?)
              (let ([rhs (mini-reify s-full (cdar s))])
                (if (pattern-vars? rhs)
                    (reify-substitution (cdr s) s-full ==s (cons (cons lhs rhs) s-out) #f)
                    (reify-substitution (cdr s) s-full (conj (== lhs rhs) ==s) s-out fully-ground?))))))]))
  
  (define-syntax pattern->term
    (syntax-rules (quote)
      [(_ 'q) 'q]
      [(_ ()) '()]
      [(_ (a . d)) (cons (pattern->term a) (pattern->term d))]
      [(_ a) a]))

  (define-syntax matcho11
    (syntax-rules ()
      [(_ ([pattern expr] ...) body ...) (matcho11 match ([pattern expr] ...) body ...)]
      [(_ name ([pattern expr] ...) body ...)
       (identifier? #'name)
       (matcho/attributed-vars name ([pattern expr] ...) (conj* body ...))]))
  
  (define-syntax matcho/attributed-vars
    ;; Because pattern var names may clash with variable names used in the destructured values, we first bind all such values to new identifiers that will not clash with any pattern variable. 
    (syntax-rules ()
      [(_ name ([pattern expr] ...) body) (matcho/attributed-vars name ([pattern expr] ...) body ())] ; Initially introduce an empty list for shadowed bindings
      [(_ name () body ([pattern expr] ...)) (matcho/pattern-vars (pattern ...) (([pattern expr] ...) body))] ; When all exprs are shadowed, proceed.
      ;; For each pattern, bind the expr to a new identifier and replace the expr binding with an identifier binding.
      [(_ name ([p e] pe ...) body (shadow ...)) (let ([v e]) (matcho/attributed-vars name (pe ...) body (shadow ... [p v])))]))
  
  (define-syntax matcho/pattern-vars
    ;; In order to generate the matcho code, we need to first extract all the pattern identifier names and pass them on.
    (syntax-rules () ; Extracts fresh var identifiers before running the match logic.
      [(_ patterns bindings-body) (matcho/pattern-vars patterns bindings-body ())] ; When called initially, create empty list for ids.
      [(_ () bindings-body ids) (matcho/ground bindings-body ids)] ; When patterns exhausted, proceed to next phase.
      [(_ ((a . d) p ...) bindings-body ids) ; Recurse on pairs
       (not (eq? (syntax->datum #'a) 'quote))
       (matcho/pattern-vars (a d p ...) bindings-body ids)]
      [(_ (p0 p ...) bindings-body (id ...)) ; Store identifiers
       (and (identifier? #'p0) (not (memp (lambda (i) (bound-identifier=? i #'p0)) #'(id ...))))
       (matcho/pattern-vars (p ...) bindings-body (p0 id ...))]
      [(_ (p0 p ...) bindings-body ids) ; Ignore ground terms
       (matcho/pattern-vars (p ...) bindings-body ids)]))

  (define-syntax matcho/ground
    ;; Before generating a matcho object, destructure any available ground values and attempt to skip directly to the inner goals.
    (syntax-rules ()
      [(_ (([pattern expr] ...) body) (id ...)) 
       (let ([id (make-var 0)] ...) ; Generate bindings for all pattern identifiers and create dummy pattern variables.
         (let ([s (mini-unify '() (list (pattern->term pattern) ...) (list expr ...))]) ; Run the mini unifier on the reified patterns and matched terms.
           (if (failure? s) fail
               (let-values ([(s^ ==s fully-ground?) (reify-substitution s)]) ; Extract the fully ground attr-vars as unifications we can make immediately, and use the remaining pattern vars and incomplete attr vars as the current substitution.
                 (if fully-ground?
                     (let ([id (mini-reify s^ id)] ...) (conj ==s body))
                     (conj ==s (make-matcho14 s^ (lambda (s)
                                                   (let ([id (mini-reify s id)] ...)
                                                     body)))))))))]))

  ;; === HUGE MACRO EXPANSION VERSION ===
  
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
                 (not (memp (lambda (i) (bound-identifier=? i pattern)) shared-ids)))))

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
               (values expanded? (conj g c) m))))])))
