;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho) (mk core goals))
  ;;TODO simplify with negated pconstraints as well


  (define (==->substitution g)
    (cert (==? g) (var? (==-lhs g)))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (=/=->substitution g) ; To fully reduce =/=, we must unroll possibly list disequalities the disunifier lazily ignored.
    (cert (=/=? g)) ; TODO call =/= sub once per reduction. maybe thread thru a separate substitution after all?
    ;; TODO try only extracting the already bound variables from =/= substitution without unifying each time
    (mini-unify '() (=/=-lhs g) (=/=-rhs g)))

  (define (simplify g) (if (fail? g) (values fail fail) (values g succeed)))

  (define (check g) (if (fail? g) (values fail fail) (values succeed g)))

  (define reduce-constraint
    ;; Reduce existing constraint g using new constraint c
    (org-case-lambda reduce-constraint
      [(g c asymmetric) (reduce-constraint g c asymmetric #f)]
      [(g c asymmetric disjunction)
       (cert (goal? g) (or (fail? g) (not (fail? c))) (or (goal? c) (mini-substitution? c))) ; -> simplified recheck
       (if (succeed? c) (simplify g)
           (exclusive-cond
            [(or (fail? g) (succeed? g)) (values g g)]
            [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs g) c asymmetric disjunction)])
                         (if (fail? simplified-lhs) (values fail fail)
                             (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs g) c asymmetric disjunction)])
                               (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
            [(disj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs g) c asymmetric disjunction)])
                         (if (and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)
                             (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs g) c asymmetric disjunction)])
                               (let ([d (disj (conj simplified-lhs recheck-lhs)
                                              (conj simplified-rhs recheck-rhs))])
                                 (if (not (succeed? recheck-lhs))
                                     (check d)
                                     (simplify d))))))]
            [(and (noto? g) (not (=/=? g))) (reduce-constraint/noto g c asymmetric disjunction)] ;TODO remove =/= check
            [(constraint? g) (reduce-constraint (constraint-goal g) c asymmetric disjunction)]
            [else
             (exclusive-cond
              [(list? c) (reduce-== g c asymmetric disjunction)]
              [(==? c) (reduce-== g (==->substitution c) asymmetric disjunction)]
              [(=/=? c) (reduce-=/= g c asymmetric disjunction)]
              [(pconstraint? c) (reduce-pconstraint g c asymmetric disjunction)]
              [(conj? c) (reduce-conj g c asymmetric disjunction)]
              [(disj? c) (reduce-disj g c asymmetric)]
              [(noto? c) (reduce-noto g (noto-goal c) asymmetric disjunction)]
              [(matcho? c) (reduce-matcho g c asymmetric disjunction)]
              [(proxy? c) (if (and (proxy? g) (fx= (proxy-id g) (proxy-id c))) (values succeed succeed) (simplify g))]
              [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons g c))])]))]))

  (define (reduce-conj g c asymmetric disjunction)
    (let*-values ([(simplified recheck) (reduce-constraint g (conj-lhs c) asymmetric disjunction)]
                  [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs c) asymmetric disjunction)]
                  [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs c) asymmetric disjunction)])
      (values simplified/simplified (conj simplified/recheck (conj recheck/simplified recheck/recheck)))))
  
  (org-define (reduce-disj g c asymmetric)
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint g (disj-lhs c) asymmetric #t)]
                 [(simplified-rhs recheck-rhs) (reduce-constraint g (disj-rhs c) asymmetric #t)])
      (cond
       [asymmetric (if (and (fail? simplified-lhs) (fail? simplified-rhs)) (values fail fail) (simplify g))]
       [(fail? simplified-lhs) (values simplified-rhs recheck-rhs)]
       [(fail? simplified-rhs) (values simplified-lhs recheck-lhs)]
       [(and (equal? simplified-lhs simplified-rhs) ;TODO how necessary is this equal check in disj reducer?
             (equal? recheck-lhs recheck-rhs))
        (values simplified-lhs recheck-rhs)]
       [else (simplify g)])))
  
  (define (reduce-constraint/noto g c asymmetric disjunction)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal g) c asymmetric disjunction)])
      (let ([d (disj (noto simplified) (noto recheck))])
        (if (not (succeed? recheck)) (check d) (simplify d)))))

  (define (reduce-noto g c asymmetric disjunction)
    (let-values ([(simplified recheck) (reduce-constraint c (if (noto? g) (noto g) g) asymmetric disjunction)])
     (if (and (succeed? simplified) (succeed? recheck))
         (if (noto? g) (values succeed succeed) (values fail fail))
         (simplify g))))

  (define (reduce-== g s asymmetric disjunction)
    (cert (goal? g) (mini-substitution? s))
    (exclusive-cond
     [(==? g) (simplify (== (mini-reify s (==-lhs g)) (mini-reify s (==-rhs g))))]
     [(=/=? g) (reduce-constraint/noto g s asymmetric disjunction)]
     [(matcho? g) (let-values ([(expanded? g ==s) (matcho/expand g s)])
                    (if expanded? ;TODO should matcho's ==s/contents be recheck or satisfied?
                        (let-values ([(simplified recheck) (reduce-constraint g s asymmetric disjunction)])
                          (values (conj ==s simplified) recheck))
                        (simplify (conj ==s g))))]
     [(pconstraint? g) (reduce-==/pconstraint g s asymmetric disjunction)]
     [(proxy? g) (simplify (if (mini-normalized? s (proxy-var g)) succeed g))] ;TODO does reduce == proxy need to be rechecked?
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define (reduce-pconstraint g c asymmetric disjunction)
    (cert (pconstraint? c))
    (exclusive-cond
     [(==? g) (let-values ([(simplified recheck) (reduce-==/pconstraint c (==->substitution g) asymmetric disjunction)])
                (if (fail? simplified) (values fail fail) (simplify g)))]
     [(=/=? g) ; -> succeed, =/=
      (let-values ([(simplified recheck) (reduce-==/pconstraint c (=/=->substitution g) asymmetric disjunction)])
        (if (fail? simplified) (values succeed succeed) (simplify g)))]
     [else (assertion-violation 'reduce-pconstraint "Unrecognized constraint type" g)]))

  (define (reduce-=/= g c asymmetric disjunction)
    ;; =/= can only simplify ==->fail and =/=->succeed
    (exclusive-cond
     [(==? g) ; -> fail, ==
      (simplify (let* ([s (=/=->substitution c)]
                       [s^ (mini-unify s (==-lhs g) (==-rhs g))])
                  (if (eq? s s^) fail g)))]
     [(=/=? g) ; -> succeed, =/=
      (simplify (if (and asymmetric disjunction) g
                 (let* ([s (=/=->substitution c)]
                        [s^ (mini-unify s (=/=-lhs g) (=/=-rhs g))])
                   (if (eq? s s^) succeed g))))]
     [(or (matcho? g) (pconstraint? g)) (simplify g)]
     [(proxy? g) (if (or (eq? (=/=-lhs c)  (proxy-var g)) (eq? (=/=-rhs c)  (proxy-var g))) (values succeed succeed) (check g))]
     [else (assertion-violation 'reduce-=/= "Unrecognized constraint type" g)]))

  (define reduce-==/pconstraint ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(g s asymmetric disjunction) (reduce-==/pconstraint g s asymmetric disjunction (pconstraint-vars g))]
      [(g s asymmetric disjunction vars)
       (if (null? vars) (simplify g)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (reduce-==/pconstraint g s asymmetric disjunction (cdr vars))
                 (reduce-constraint ((pconstraint-procedure g) (car vars) v g succeed g) s asymmetric disjunction))))]))

  (define (reduce-matcho g c asymmetric disjunction)
    (exclusive-cond
     [(==? g) (if (failure? (mini-unify-substitution (matcho-substitution c) (==->substitution g))) (values fail fail) (simplify g))]
     [(=/=? g) ; -> succeed, =/=
      (if (failure? (mini-unify-substitution (matcho-substitution c) (=/=->substitution g)))
          (values succeed succeed) (simplify g))]
     ;;TODO matchos with eq? lambda can cancel
     [else (assertion-violation 'reduce-matcho "Unrecognized constraint type" g)]))

  )
