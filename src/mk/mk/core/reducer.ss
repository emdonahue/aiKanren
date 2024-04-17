;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho) (mk core goals))
  ;;TODO simplify with negated pconstraints as well


  (define (==->substitution g)
    (cert (==? g))
    (mini-unify '() (==-lhs g) (==-rhs g)))

  (define (=/=->substitution g) (==->substitution (noto g)))

  (define (simplify g) (if (fail? g) (values fail fail) (values g succeed)))

  (define (check g) (if (fail? g) (values fail fail) (values succeed g)))

  (define (reduce-constraint g c) ; TODO ensure that succeed/fail constraints always match
    ;; Reduce existing constraint g using new constraint c, possibly with bindings s.
    (cert (goal? g) (not (fail? c)) (or (goal? c) (mini-substitution? c))) ; -> simplified recheck
    (if (succeed? c) (simplify g)
        (exclusive-cond
         [(or (fail? g) (succeed? g)) (values g g)]
         [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs g) c)])
                      (if (fail? simplified-lhs) (values fail fail)
                          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs g) c)])
                            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
         [(disj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs g) c)])
                      (if (and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)
                          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs g) c)])
                            (let ([d (disj (conj simplified-lhs recheck-lhs)
                                           (conj simplified-rhs recheck-rhs))])
                              (if (not (succeed? recheck-lhs))
                                  (check d)
                                  (simplify d))))))]
         [(and (noto? g) (not (=/=? g))) (reduce-constraint/noto g c)] ;TODO remove =/= check
         [(constraint? g) (reduce-constraint (constraint-goal g) c)]
         [else
          (exclusive-cond
           [(list? c) (reduce-== g c)]
           [(==? c) (reduce-== g (==->substitution c))]
           [(=/=? c) (reduce-=/= g (=/=->substitution c))]
           [(pconstraint? c) (reduce-pconstraint g c)]
           [(conj? c) (let*-values ([(simplified recheck) (reduce-constraint g (conj-lhs c))]
                                    [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs c))]
                                    [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs c))])
                        (values simplified/simplified (conj simplified/recheck (conj recheck/simplified recheck/recheck))))]
           [(disj? c) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint g (disj-lhs c))]
                                   [(simplified-rhs recheck-rhs) (reduce-constraint g (disj-rhs c))])
                        (if (and (equal? simplified-lhs simplified-rhs) (equal? recheck-lhs recheck-rhs))
                            (values simplified-lhs recheck-rhs) (simplify g)))]
           [(noto? c) (reduce-noto g (noto-goal c))]
           [(matcho? c) (reduce-matcho g c)]
           [(proxy? c) (if (and (proxy? g) (fx= (proxy-id g) (proxy-id c))) (values succeed succeed) (simplify g))]
           [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons g c))])]))
    )

  (define (reduce-constraint/noto g c)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal g) c)])
      (let ([d (disj (noto simplified) (noto recheck))])
        (if (not (succeed? recheck)) (check d) (simplify d)))))

  (define (reduce-noto g c)
    (let-values ([(simplified recheck) (reduce-constraint c (if (noto? g) (noto g) g))])
     (if (and (succeed? simplified) (succeed? recheck))
         (if (noto? g) (values succeed succeed) (values fail fail))
         (simplify g))))

  (define (reduce-== g s)
    (cert (goal? g) (mini-substitution? s))
    (exclusive-cond
     [(==? g) (simplify (== (mini-reify s (==-lhs g)) (mini-reify s (==-rhs g))))]
     [(=/=? g) (reduce-constraint/noto g s)]
     [(matcho? g) (let-values ([(expanded? g ==s) (matcho/expand g s)])
                    (if expanded? ;TODO should matcho's ==s/contents be recheck or satisfied?
                        (let-values ([(simplified recheck) (reduce-constraint g s)])
                          (values (conj ==s simplified) recheck))
                        (simplify (conj ==s g))))]
     [(pconstraint? g) (reduce-==/pconstraint g s)]
     [(proxy? g) (simplify (if (mini-normalized? s (proxy-var g)) succeed g))] ;TODO does reduce == proxy need to be rechecked?
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define (reduce-pconstraint g c)
    (cert (pconstraint? c))
    (exclusive-cond
     [(==? g) (let-values ([(simplified recheck) (reduce-==/pconstraint c (==->substitution g))])
                (if (fail? simplified) (values fail fail) (simplify g)))]
     [(=/=? g) (let-values ([(simplified recheck) (reduce-==/pconstraint c (=/=->substitution g))])
                 (if (fail? simplified) (values succeed succeed) (simplify g)))]
     [else (assertion-violation 'reduce-pconstraint "Unrecognized constraint type" g)]))

  (define (reduce-=/= g s)
    (exclusive-cond
     [(==? g) (simplify (let ([s^ (mini-unify s (==-lhs g) (==-rhs g))])
                            (if (eq? s s^) fail g)))]
     [(=/=? g) (simplify (let ([s^ (mini-unify s (=/=-lhs g) (=/=-rhs g))])
                             (if (eq? s s^) succeed g)))]
     [(or (matcho? g) (pconstraint? g)) (simplify g)]
     [(proxy? g) (if (mini-normalized? s (proxy-var g)) (values succeed succeed) (check g))]
     [else (assertion-violation 'reduce-=/= "Unrecognized constraint type" g)]))

  (define reduce-==/pconstraint ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(g s) (reduce-==/pconstraint g s (pconstraint-vars g))]
      [(g s vars)
       (if (null? vars) (simplify g)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (reduce-==/pconstraint g s (cdr vars))
                 (reduce-constraint ((pconstraint-procedure g) (car vars) v g succeed g) s))))]))

  (define (reduce-matcho g c)
    (exclusive-cond
     [(==? g) (if (failure? (mini-unify-substitution (matcho-substitution c) (==->substitution g))) (values fail fail) (simplify g))]
     [(=/=? g) (if (failure? (mini-unify-substitution (matcho-substitution c) (=/=->substitution g))) (values succeed succeed) (simplify g))]
     ;;TODO matchos with eq? lambda can cancel
     [else (assertion-violation 'reduce-matcho "Unrecognized constraint type" g)]))

  )
