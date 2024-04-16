;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho) (mk core goals))
  ;;TODO simplify with negated pconstraints as well


  (define (==->substitution g)
    (cert (==? g))
    (mini-unify '() (==-lhs g) (==-rhs g)))

  (define (=/=->substitution g) (==->substitution (noto g)))

  (define (reduce-constraint g c)
    ;; Reduce existing constraint g using new constraint c, possibly with bindings s.
    (cert (goal? g) (not (fail? c)) (or (goal? c) (mini-substitution? c))) ; -> simplified recheck
    (if (succeed? c) g
        (exclusive-cond
         [(or (fail? g) (succeed? g)) (values g g)]
         [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs g) c)])
                      (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs g) c)])
                            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
         [(disj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs g) c)])
                      (if (and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)
                          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs g) c)])
                            (let ([d (disj (conj simplified-lhs recheck-lhs)
                                           (conj simplified-rhs recheck-rhs))])
                              (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs)))
                                  (values succeed d)
                                  (values d succeed))))))]
         [(and (noto? g) (not (=/=? g))) (reduce-constraint/noto g c)] ;TODO remove =/= check
         [(constraint? g) (reduce-constraint (constraint-goal g) c)]
         [else
          (exclusive-cond
           [(list? c) (reduce-== g c)]
           [(==? c) (reduce-== g (==->substitution c))]
           [(=/=? c) (reduce-=/= g (=/=->substitution c))]
           [(pconstraint? c) (reduce-pconstraint g c)]
           [(conj? c) (reduce-constraint (reduce-constraint g (conj-lhs c)) (conj-rhs c))]
           [(disj? c) (let ([g-lhs (reduce-constraint g (disj-lhs c))]
                            [g-rhs (reduce-constraint g (disj-rhs c))])
                        (if (equal? g-lhs g-rhs) g-lhs g))]
           [(noto? c) (reduce-noto g (noto-goal c))]
           [(matcho? c) (reduce-matcho g c)]
           [(proxy? c) (if (and (proxy? g) (fx= (proxy-id g) (proxy-id c))) succeed g)]
           [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons g c))])]))
    )

  (define (reduce-constraint/noto g c)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal g) c)])
      (let ([d (disj (noto simplified) (noto recheck))])
        (if (not (succeed? recheck)) (values succeed d) (values d succeed)))))

  (define (reduce-noto g c)
    (if (succeed? (reduce-constraint c (if (noto? g) (noto g) g)))
        (if (noto? g) succeed fail)
        g))

  (define (reduce-== g s)
    (cert (goal? g) (mini-substitution? s))
    (exclusive-cond
     [(==? g) (values (== (mini-reify s (==-lhs g)) (mini-reify s (==-rhs g))) succeed)]
     [(=/=? g) (reduce-constraint/noto g s)]
     [(matcho? g) (let-values ([(expanded? g ==s) (matcho/expand g s)])
                    (if expanded? ;TODO should matcho's ==s/contents be recheck or satisfied?
                        (let-values ([(simplified recheck) (reduce-constraint g s)])
                          (values (conj ==s simplified) recheck))
                        (values (conj ==s g) succeed)))]
     [(pconstraint? g) (reduce-==/pconstraint g s)]
     [(proxy? g) (values (if (mini-normalized? s (proxy-var g)) succeed g) succeed)]
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define (reduce-pconstraint g c)
    (cert (pconstraint? c))
    (exclusive-cond
     [(==? g) (if (fail? (reduce-==/pconstraint c (==->substitution g))) fail g)]
     [(=/=? g) (if (fail? (reduce-==/pconstraint c (=/=->substitution g))) succeed g)]
     [else (assertion-violation 'reduce-pconstraint "Unrecognized constraint type" g)]))

  (define (reduce-=/= g s)
    (values 
     (exclusive-cond
      [(==? g) (let ([s^ (mini-unify s (==-lhs g) (==-rhs g))])
                 (if (eq? s s^) fail g))]
      [(=/=? g) (let ([s^ (mini-unify s (=/=-lhs g) (=/=-rhs g))])
                  (if (eq? s s^) succeed g))]
      [(or (matcho? g) (pconstraint? g)) g]
      [(proxy? g) (if (mini-normalized? s (proxy-var g)) succeed g)]
      [else (assertion-violation 'reduce-=/= "Unrecognized constraint type" g)]) succeed))

  (define reduce-==/pconstraint ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(g s) (reduce-==/pconstraint g s (pconstraint-vars g))]
      [(g s vars)
       (if (null? vars) (values g succeed)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (reduce-==/pconstraint g s (cdr vars))
                 (reduce-constraint ((pconstraint-procedure g) (car vars) v g succeed g) s))))]))

  (define (reduce-matcho g c)
    (exclusive-cond
     [(==? g) (if (failure? (mini-unify-substitution (matcho-substitution c) (==->substitution g))) fail g)]
     [(=/=? g) (if (failure? (mini-unify-substitution (matcho-substitution c) (=/=->substitution g))) succeed g)]
     [else (assertion-violation 'reduce-matcho "Unrecognized constraint type" g)]))

  )
