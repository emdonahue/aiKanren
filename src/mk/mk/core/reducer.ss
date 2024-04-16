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
      [(or (fail? g) (succeed? g)) g]
      [(conj? g) (conj (reduce-constraint (conj-lhs g) c) (reduce-constraint (conj-rhs g) c))]
      [(disj? g) (disj (reduce-constraint (disj-lhs g) c) (reduce-constraint (disj-rhs g) c))]
      [(and (noto? g) (not (=/=? g))) (noto (reduce-constraint (noto-goal g) c))] ;TODO remove =/= check
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

  (define (reduce-noto g c)
    (if (succeed? (reduce-constraint c (if (noto? g) (noto g) g)))
        (if (noto? g) succeed fail)
        g))
  
  (define (reduce-== g s)
    (cert (goal? g) (mini-substitution? s))
    (exclusive-cond
     [(==? g) (== (mini-reify s (==-lhs g)) (mini-reify s (==-rhs g)))]
     [(=/=? g) (noto (reduce-== (noto g) s))]
     [(matcho? g) (let-values ([(expanded? g ==s) (matcho/expand g s)])
                    (if expanded?
                        (conj ==s (reduce-constraint g s))
                        (conj ==s g)))]
     [(pconstraint? g) (reduce-==/pconstraint g s)]
     [(proxy? g) (if (mini-normalized? s (proxy-var g)) succeed g)]
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define (reduce-pconstraint g c)
    (cert (pconstraint? c))
    (exclusive-cond
     [(==? g) (if (fail? (reduce-==/pconstraint c (==->substitution g))) fail g)]
     [(=/=? g) (if (fail? (reduce-==/pconstraint c (=/=->substitution g))) succeed g)]
     [else (assertion-violation 'reduce-pconstraint "Unrecognized constraint type" g)]))

  (define (reduce-=/= g s)
    (exclusive-cond
     [(==? g) (let ([s^ (mini-unify s (==-lhs g) (==-rhs g))])
                (if (eq? s s^) fail g))]
     [(=/=? g) (let ([s^ (mini-unify s (=/=-lhs g) (=/=-rhs g))])
                 (if (eq? s s^) succeed g))]
     [(or (matcho? g) (pconstraint? g)) g]
     [(proxy? g) (if (mini-normalized? s (proxy-var g)) succeed g)]
     [else (assertion-violation 'reduce-=/= "Unrecognized constraint type" g)]))

  (define reduce-==/pconstraint ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(g s) (reduce-==/pconstraint g s (pconstraint-vars g))]
      [(g s vars)
       (if (null? vars) g 
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
