;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho))
  ;; TODO simplify with negated pconstraints as well
  ;; TODO mini-normalized (free?) needs to walk, not just check presence
  ;; TODO can a left-failing disj ever be made simplified by =/= or ==? note that we are always comparing normalized constraints
  ;; TODO if one element of a conj vouches for satisfaction, should that overrule another saying its recheck?
  ;; TODO test whether we need 2 var eq with: x == y | ... AND y == z (or z == y) | ... AND x=/=z

  (define (==->substitution g)
    (cert (==? g) (var? (==-lhs g)))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (=/=->substitution g) ; To fully reduce =/=, we must unroll possibly list disequalities the disunifier lazily ignored.
    (cert (=/=? g)) ; TODO call =/= sub once per reduction. maybe thread thru a separate substitution after all?
    ;; TODO try only extracting the already bound variables from =/= substitution without unifying each time
    ;; TODO we may need to worry about failure if we do something less than full unification, so maybe we need a mini-disunify
    (mini-unify '() (=/=-lhs g) (=/=-rhs g)))
  
  (define simplify
    (case-lambda
      [(g) (simplify g succeed)] ; TODO 2 arg simplify should probably be its own fn
      [(g recheck) (if (or (fail? g) (fail? recheck)) (values fail fail) (values g recheck))]))

  (define (check g) (if (fail? g) (values fail fail) (values succeed g)))

  (define (vouch g e-normalized r-normalized r-vouches)
    (if (fail? g) (values fail fail)
     (if (or e-normalized (and r-normalized r-vouches)) (values g succeed) (values succeed g))))

  (define (vouches? r e)
    (if (mini-substitution? r)
        (for-all (lambda (v) (mini-normalized? r v)) (normalized-vars e))
        (let ([n-vars (normalized-vars r)])
          (for-all (lambda (v) (member v n-vars)) (normalized-vars e)))))
  
  
  ;; === REDUCEE ===
  (define reduce-constraint
    ;; Reduce existing constraint g using new constraint c.
    ;; e-free => g is a e-free constraint (not in the store). for a e-free =/=, this means that =/= in the store won't simplify it away, so that we can turn around and use it to simplify the =/= already in the story, which may in turn simplify containing disj. e-free mode preserves some information. #f=store mode goes all out to simplify the store.
    (case-lambda
      [(rdcee rdcrr e-free) (reduce-constraint rdcee rdcrr e-free #f e-free (not e-free))] ; TODO can we combine e-free and r-disjunction, or are they ever used separately?
      [(rdcee rdcrr e-free r-disjunction e-normalized r-normalized) ;TODO split normalized into reducer/reducee
       (cert (goal? rdcee) (or (fail? rdcee) (not (fail? rdcrr))) (or (goal? rdcrr) (mini-substitution? rdcrr))) ; -> simplified recheck
       (if (succeed? rdcrr) (values rdcee succeed)
           (exclusive-cond
            [(or (fail? rdcee) (succeed? rdcee)) (values rdcee rdcee)]
            [(conj? rdcee) (reduce-conj rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
            [(disj? rdcee) (reduce-disj rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
            [(and (noto? rdcee) (not (=/=? rdcee))) (reduce-noto rdcee rdcrr e-free r-disjunction e-normalized r-normalized)] ;TODO remove =/= check
            [(constraint? rdcee) (reduce-constraint (constraint-goal rdcee) rdcrr e-free r-disjunction e-normalized r-normalized)]
            [(and (=/=? rdcee) (pair? (=/=-lhs rdcee)))
             (reduce-constraint (mini-disunify '() (=/=-lhs rdcee) (=/=-rhs rdcee)) rdcrr e-free r-disjunction e-normalized r-normalized)]
            [(proxy? rdcee) (constraint-reduce rdcee rdcrr #f r-disjunction #f r-normalized)] ; Proxies are never normalized bc they can't be stored. They can only be rechecked. They are also never free.
            [else (constraint-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]))]))
  
  (define (reduce-conj rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (cert (conj? rdcee))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs rdcee) rdcrr e-free r-disjunction e-normalized r-normalized)])
      (if (fail? simplified-lhs) (values fail fail)
          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs rdcee) rdcrr e-free r-disjunction e-normalized r-normalized)])
            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs))))))

  (org-define (reduce-disj rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
              (cert (disj? rdcee))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs rdcee) rdcrr e-free r-disjunction e-normalized r-normalized)])
      (exclusive-cond
       [(and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)]
       [(fail? simplified-lhs) (reduce-constraint (disj-rhs rdcee) rdcrr e-free r-disjunction #f r-normalized)]
       [else
        (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs rdcee) rdcrr e-free r-disjunction #f r-normalized)])
          (vouch (disj (conj simplified-lhs recheck-lhs) (conj simplified-rhs recheck-rhs))
                 e-normalized r-normalized (succeed? recheck-lhs)))])))
  
  (define (reduce-noto rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal rdcee) rdcrr e-free r-disjunction e-normalized r-normalized)])
      (vouch (disj (noto simplified) (noto recheck)) e-normalized r-normalized (succeed? recheck))))

  ;; === REDUCER ===
  (define (constraint-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(list? rdcrr) (==-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
     [(==? rdcrr) (==-reduce rdcee (==->substitution rdcrr) e-free r-disjunction e-normalized r-normalized)]
     [(=/=? rdcrr) (=/=-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
     [(pconstraint? rdcrr) (pconstraint-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
     [(conj? rdcrr) (conj-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
     [(disj? rdcrr) (disj-reduce rdcee rdcrr e-free e-normalized r-normalized)]
     [(noto? rdcrr) (noto-reduce rdcee (noto-goal rdcrr) e-free r-disjunction e-normalized r-normalized)]
     [(matcho? rdcrr) (matcho-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)]
     [(proxy? rdcrr) (vouch rdcee e-normalized r-normalized #f)] ; Proxies are never normalized and so can vouch for nothing
     [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons rdcee rdcrr))]))
  
  (define (conj-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (let*-values ([(simplified recheck) (reduce-constraint rdcee (conj-lhs rdcrr) e-free r-disjunction e-normalized r-normalized)]
                  [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs rdcrr) e-free r-disjunction e-normalized r-normalized)]
                  [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs rdcrr) e-free r-disjunction e-normalized r-normalized)])
      (values (conj simplified/simplified (conj simplified/recheck recheck/simplified)) recheck/recheck)))
  
  (org-define (disj-reduce rdcee rdcrr e-free e-normalized r-normalized)
              (cert (disj? rdcrr))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint rdcee (disj-lhs rdcrr) e-free #t e-normalized r-normalized)]
                 [(simplified-rhs recheck-rhs) (reduce-constraint rdcee (disj-rhs rdcrr) e-free #t e-normalized #f)])
      (org-cond
       [(fail? simplified-lhs) (values simplified-rhs recheck-rhs)]
       [(fail? simplified-rhs) (values simplified-lhs recheck-lhs)]
       [(and (succeed? simplified-lhs) (succeed? simplified-rhs) (succeed? recheck-lhs) (succeed? recheck-rhs))
        (values succeed succeed)]
       [else (vouch rdcee e-normalized r-normalized (or (and (succeed? recheck-lhs) (not (succeed? simplified-lhs)))
                                                        (and (succeed? recheck-rhs) (not (succeed? simplified-rhs)))))])))

  (org-define (==-reduce rdcee s e-free r-disjunction e-normalized r-normalized)
    (cert (goal? rdcee) (mini-substitution? s))
    (exclusive-cond
     [(==? rdcee) (let-values ([(lhs-normalized? lhs) (mini-walk-normalized s (==-lhs rdcee))]
                               [(rhs-normalized? rhs) (mini-walk-normalized s (==-rhs rdcee))])
                    (vouch (== lhs rhs) e-normalized r-normalized (and (var? lhs) lhs-normalized? rhs-normalized?)))]
     [(=/=? rdcee) (let-values ([(rdcee r-vouches) (mini-disunify/normalized s (=/=-lhs rdcee) (=/=-rhs rdcee))])
                 (vouch rdcee e-normalized r-normalized r-vouches))]
     [(matcho? rdcee) (let-values ([(expanded? rdcee ==s) (matcho/expand rdcee s)])
                        (if expanded?
                            (reduce-constraint (conj ==s rdcee) s e-free r-disjunction #f r-normalized)
                            (let-values ([(==s/simplified ==s/recheck) (reduce-constraint ==s s e-free r-disjunction #f r-normalized)]
                                         [(rdcee rdcee/recheck) (vouch rdcee e-normalized r-normalized (vouches? s rdcee))])
                              (values (conj ==s/simplified rdcee) (conj ==s/recheck rdcee/recheck)))))]
     [(pconstraint? rdcee) (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized)]
     [(proxy? rdcee) ; If we can vouch that they have already been walked, discard. Otherwise we have to walk them (cant be stored). 
      (if (and r-normalized (mini-normalized? s (proxy-var rdcee))) (values succeed succeed) (values succeed rdcee))] 
     [else (assertion-violation '==-reduce "Unrecognized constraint type" rdcee)]))

  (org-define (=/=-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
              ;; =/= can only simplify ==->fail and =/=->succeed
              (cert (=/=? rdcrr))
    (exclusive-cond
     [(==? rdcee) ; -> fail?. Simple equality check ok because 1) we ignore list unifications for performance reasons, constants will already succeed or fail, and == orders vars by id
      (vouch (if (equal? rdcee (noto-goal rdcrr)) fail rdcee) e-normalized r-normalized (vouches? (noto-goal rdcrr) rdcee))]
     [(=/=? rdcee) ; -> succeed, =/=
      (cert (not (pair? (=/=-lhs rdcee))))
      (if (and (not (and e-free r-disjunction)) (equal? rdcee rdcrr)) ; If reducee is free and reducer is in a disjunction, we must negate our usual symmetric equality check and preserve the reducee so it can later simplify the reducer.
          (values succeed succeed) ; Identical =/= can cancel
          (vouch rdcee e-normalized r-normalized (and (not (and e-free r-disjunction))
                                                      (vouches? (noto-goal rdcrr) (noto-goal rdcee)))))]
     [(matcho? rdcee) (vouch rdcee e-normalized r-normalized (vouches? rdcrr rdcee))]
     [(pconstraint? rdcee) (vouch rdcee e-normalized r-normalized (vouches? rdcrr rdcee))]
     [(proxy? rdcee) (if (vouches? rdcrr rdcee) (values succeed succeed) (values succeed rdcee))]
     [else (assertion-violation '=/=-reduce "Unrecognized constraint type" rdcee)]))
  
  (define (pconstraint-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (cert (pconstraint? rdcrr))
    (exclusive-cond
     [(==? rdcee) (let-values ([(simplified recheck) (==/pconstraint-reduce rdcrr (==->substitution rdcee) e-free r-disjunction e-normalized r-normalized)])
                (if (fail? simplified) (values fail fail) (simplify rdcee)))]
     [(=/=? rdcee) ; -> succeed, =/=
      (let-values ([(simplified recheck) (==/pconstraint-reduce rdcrr (=/=->substitution rdcee) e-free r-disjunction e-normalized r-normalized)])
        (if (fail? simplified) (values succeed succeed) (simplify rdcee)))]
     [else (assertion-violation 'pconstraint-reduce "Unrecognized constraint type" rdcee)]))

  (define ==/pconstraint-reduce ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(rdcee s e-free r-disjunction e-normalized r-normalized) (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized (pconstraint-vars rdcee))]
      [(rdcee s e-free r-disjunction e-normalized r-normalized vars)
       (if (null? vars) (vouch rdcee e-normalized r-normalized #t)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized (cdr vars))
                 (reduce-constraint ((pconstraint-procedure rdcee) (car vars) v rdcee succeed rdcee) s e-free r-disjunction e-normalized r-normalized))))]))

  (define (matcho-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(==? rdcee) (if (failure? (mini-unify-substitution (matcho-substitution rdcrr) (==->substitution rdcee)))
                      (values fail fail)
                      (vouch rdcee e-normalized r-normalized (vouches? rdcrr rdcee)))]
     [(=/=? rdcee) ; -> succeed, =/=
      (if (failure? (mini-unify-substitution (matcho-substitution rdcrr) (=/=->substitution rdcee)))
          (values succeed succeed)
          (vouch rdcee e-normalized r-normalized (vouches? rdcrr rdcee)))] ;TODO could a =/= of lists simultaneously fail?
     ;;TODO matchos with eq? lambda can cancel
     [else (assertion-violation 'matcho-reduce "Unrecognized constraint type" rdcee)]))

  (define (noto-reduce rdcee rdcrr e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint rdcrr (if (noto? rdcee) (noto-goal rdcee) rdcee) e-free r-disjunction e-normalized r-normalized)])
      (if (and (succeed? simplified) (succeed? recheck))
          (if (noto? rdcee) (values succeed succeed) (values fail fail))
          (vouch rdcee e-normalized r-normalized (vouches? rdcrr rdcee))))))
