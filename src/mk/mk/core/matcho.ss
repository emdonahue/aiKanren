(library (mk core matcho) ; Adapted from the miniKanren workshop paper "Guarded Fresh Goals: Dependency-Directed Introduction of Fresh Logic Variables"

  (export matcho/expand matcho-attributed-vars matcho/run
          matcho pattern->term)
  (import (chezscheme) (mk core streams) (mk core variables) (mk core goals) (mk core mini-substitution) (mk core state) (mk core utils))

  ;; TODO make matcho work for pure values outside of mk. a la carte unification/pattern matching
  ;; TODO make a special pre-sequence to bind the pure single var renames with no pair patterns
  ;; TODO consider else clause for returning a new goal if matcho fails the pattern match
  ;; TODO consider a cond form that nests matcho else clauses to create a cond like form without lots of negation
  ;;TODO first order matcho that can be unified with a variable to destructure it. Useful for passing to functions where we dont have a reference to the variable
  
  (define (pattern-var? v)
    (cert (var? v))
    (zero? (var-id v)))

  (define (pattern-binding? b)
    (cert (pair? b) (var? (car b)))
    (pattern-var? (car b)))

  (define (pattern-vars? x)
    (if (pair? x)
        (or (pattern-vars? (car x)) (pattern-vars? (cdr x)))
        (and (var? x) (zero? (var-id x)))))

  (define (matcho-attributed-vars g)
    ;; The matcho attributed vars are the non pattern vars still in the substitution because they have not been fully grounded.
    (cert (matcho? g))
    (map car (remp pattern-binding? (matcho-substitution g))))

  (define (matcho/run g s)
    (let*-values ([(sub vid) (fresh-substitution (matcho-substitution g) (state-varid s))] ; Replace pattern vars with fresh vars
                  [(sub ==s^ fully-ground?) (reify-substitution sub)]) ; Remove now ground attributed vars and unify them
      (values (conj* ==s^ ((matcho-ctn g) sub)) (set-state-varid s vid))))

  (define fresh-substitution
    ;; Replace pattern vars in the substitution with fresh vars
    (case-lambda
      [(s vid) (fresh-substitution s s vid)]
      [(s s^ vid) (if (null? s) (values s^ vid)
                      (let-values ([(s^ vid) (fresh-pattern (cdar s) s^ vid)])
                        (fresh-substitution (cdr s) s^ vid)))]))

  (define (fresh-pattern p s vid)
    ;; Replace pattern vars in a term with fresh vars
    (if (pair? p)
        (let-values ([(s vid) (fresh-pattern (car p) s vid)])
          (fresh-pattern (cdr p) s vid))
        (if (and (var? p) (pattern-var? p) (not (assq p s)))
            (let ([vid (fx1+ vid)])
              (values (cons (cons p (make-var vid)) s) vid))
            (values s vid))))  
  
  (define matcho/expand
    ;; Expand the matcho as much as possible using the variables in the substitution
    (case-lambda
      [(g s) (matcho/expand g s (matcho-substitution g) succeed '())]
      [(g s sub ==s vs)
       (cert (matcho? g) (state? s) (list? sub) (goal? ==s) (list? vs))
       (let ([attr-binding (find (lambda (b) (not (or (pattern-binding? b) ; Get an unwalked attributed var
                                                      (memq (car b) vs)))) sub)])
         (if attr-binding ; If one exists,
             (let ([sub (mini-unify (remq attr-binding sub) ; walk the var and unify its value into the mini substitution.
                                    (cdr attr-binding)  (walk-var s (car attr-binding)))])
               (if (failure? sub) (values #t fail fail) ; If that unification doesn't fail,
                   (let-values ([(sub ==s^ fully-ground?) (reify-substitution sub)])
                     (if fully-ground?
                         (values #t ((matcho-ctn g) sub) (conj ==s^ ==s)) ; Therefore execute the body.
                         (matcho/expand g s sub ; and continue walking unwalked variables.
                                        (conj ==s^ ==s)
                                        (cons (car attr-binding) vs))))))
             ;; If there are no unwalked attributed vars remaining, suspend expansion and return.
             (values #f (make-matcho sub (matcho-ctn g)) ==s)))]))

  (define reify-substitution
    ;; Separate fully ground attributed vars from the substitution.
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

  (define-syntax matcho
    (syntax-rules ()
      [(_ ([pattern expr] ...) body ...) (matcho match ([pattern expr] ...) body ...)]
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
               (let-values ([(s ==s fully-ground?) (reify-substitution s)]) ; Extract the fully ground attr-vars as unifications we can make immediately, and use the remaining pattern vars and incomplete attr vars as the current substitution.
                 (if fully-ground?
                     (let ([id (mini-reify s id)] ...) (conj ==s body))
                     (conj ==s (make-matcho s (lambda (s)
                                                   (let ([id (mini-reify s id)] ...)
                                                     body)))))))))])))