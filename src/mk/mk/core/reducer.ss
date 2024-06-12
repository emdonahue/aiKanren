;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho))
  ;; TODO simplify with negated pconstraints as well
  ;; TODO mini-normalized (free?) needs to walk, not just check presence
  ;; TODO can a left-failing disj ever be made simplified by =/= or ==? note that we are always comparing normalized constraints
  ;; TODO if one element of a conj vouches for satisfaction, should that overrule another saying its recheck?


  (define (==->substitution g)
    (cert (==? g) (var? (==-lhs g)))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (=/=->substitution g) ; To fully reduce =/=, we must unroll possibly list disequalities the disunifier lazily ignored.
    (cert (=/=? g)) ; TODO call =/= sub once per reduction. maybe thread thru a separate substitution after all?
    ;; TODO try only extracting the already bound variables from =/= substitution without unifying each time
    ;; TODO we may need to worry about failure if we do something less than full unification, so maybe we need a mini-disunify
    (mini-unify '() (=/=-lhs g) (=/=-rhs g)))

  (define (simplify g) (if (fail? g) (values fail fail) (values g succeed)))

  (define (check g) (if (fail? g) (values fail fail) (values succeed g)))

  (define (vouch g e-normalized r-normalized r-vouches)
    (if (or e-normalized (and r-normalized r-vouches)) (simplify g) (check g)))

  (define (vouches r e) ; r vouches for e when all vars in e are also in r, implying no walks/rechecks necessary
    (and (or (not (var? (==-lhs e))) (==-member? (==-lhs e) r))
         (or (not (var? (==-rhs e))) (==-member? (==-rhs e) r))))

  ;; === REDUCEE ===
  (define reduce-constraint
    ;; Reduce existing constraint g using new constraint c.
    ;; e-free => g is a e-free constraint (not in the store). for a e-free =/=, this means that =/= in the store won't simplify it away, so that we can turn around and use it to simplify the =/= already in the story, which may in turn simplify containing disj. e-free mode preserves some information. #f=store mode goes all out to simplify the store.
    (case-lambda
      [(rdcee rcdrr e-free) (reduce-constraint rdcee rcdrr e-free #f #t #t)]
      [(rdcee rcdrr e-free r-disjunction e-normalized r-normalized) ;TODO split normalized into reducer/reducee
       (cert (goal? rdcee) (or (fail? rdcee) (not (fail? rcdrr))) (or (goal? rcdrr) (mini-substitution? rcdrr))) ; -> simplified recheck
       (if (succeed? rcdrr) (simplify rdcee)
           (exclusive-cond
            [(or (fail? rdcee) (succeed? rdcee)) (values rdcee rdcee)]
            [(conj? rdcee) (reduce-conj rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
            [(disj? rdcee) (reduce-disj rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
            [(and (noto? rdcee) (not (=/=? rdcee))) (reduce-noto rdcee rcdrr e-free r-disjunction e-normalized r-normalized)] ;TODO remove =/= check
            [(constraint? rdcee) (reduce-constraint (constraint-goal rdcee) rcdrr e-free r-disjunction e-normalized r-normalized)]
            [(and (=/=? rdcee) (pair? (=/=-lhs rdcee)))
             (reduce-constraint (mini-disunify '() (=/=-lhs rdcee) (=/=-rhs rdcee)) rcdrr e-free r-disjunction e-normalized r-normalized)]
            [else (constraint-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]))]))
  
  (define (reduce-conj rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (cert (conj? rdcee))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs rdcee) rcdrr e-free r-disjunction e-normalized r-normalized)])
      (if (fail? simplified-lhs) (values fail fail)
          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs rdcee) rcdrr e-free r-disjunction e-normalized r-normalized)])
            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs))))))

  (org-define (reduce-disj rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
              (cert (disj? rdcee))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs rdcee) rcdrr e-free r-disjunction e-normalized r-normalized)])
      (exclusive-cond
       [(and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)]
       [(fail? simplified-lhs) (reduce-constraint (disj-rhs rdcee) rcdrr e-free r-disjunction #f r-normalized)]
       [else (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs rdcee) rcdrr e-free r-disjunction #f r-normalized)])
               (let ([d (disj (conj simplified-lhs recheck-lhs)
                              (conj simplified-rhs recheck-rhs))])
                 (if (not (succeed? recheck-lhs))
                     (check d)
                     (simplify d))))])))
  
  (define (reduce-noto rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal rdcee) rcdrr e-free r-disjunction e-normalized r-normalized)])
      (let ([d (disj (noto simplified) (noto recheck))])
        (if (not (succeed? recheck)) (check d) (simplify d)))))

  ;; === REDUCER ===
  (define (constraint-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(list? rcdrr) (==-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
     [(==? rcdrr) (==-reduce rdcee (==->substitution rcdrr) e-free r-disjunction e-normalized r-normalized)]
     [(=/=? rcdrr) (=/=-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
     [(pconstraint? rcdrr) (pconstraint-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
     [(conj? rcdrr) (conj-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
     [(disj? rcdrr) (disj-r rdcee rcdrr e-free e-normalized r-normalized)]
     [(noto? rcdrr) (noto-reduce rdcee (noto-goal rcdrr) e-free r-disjunction e-normalized r-normalized)]
     [(matcho? rcdrr) (matcho-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)]
     [(proxy? rcdrr) (if (and (proxy? rdcee) (fx= (proxy-id rdcee) (proxy-id rcdrr))) (values succeed succeed) (simplify rdcee))]
     [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons rdcee rcdrr))]))
  
  (define (conj-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (let*-values ([(simplified recheck) (reduce-constraint rdcee (conj-lhs rcdrr) e-free r-disjunction e-normalized r-normalized)]
                  [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs rcdrr) e-free r-disjunction e-normalized r-normalized)]
                  [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs rcdrr) e-free r-disjunction e-normalized r-normalized)])
      (values (conj simplified/simplified (conj simplified/recheck recheck/simplified)) recheck/recheck)
      #;
      (values simplified/simplified (conj simplified/recheck (conj recheck/simplified recheck/recheck)))))
  
  (org-define (disj-r rdcee rcdrr e-free e-normalized r-normalized)
              (cert (disj? rcdrr)) ; TODO can we remove r-disj boolean and handle it inside disj-r fn
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint rdcee (disj-lhs rcdrr) e-free #t e-normalized r-normalized)]
                 [(simplified-rhs recheck-rhs) (reduce-constraint rdcee (disj-rhs rcdrr) e-free #t e-normalized #f)])
      (cond
       #;
       [e-free (if (and (trivial? simplified-lhs) (eq? simplified-lhs simplified-rhs))
                       (simplify simplified-lhs) (simplify g))]
       [(fail? simplified-lhs) (values simplified-rhs recheck-rhs)]
       [(fail? simplified-rhs) (values simplified-lhs recheck-lhs)]
       [(and (succeed? simplified-lhs) (succeed? simplified-rhs) (succeed? recheck-lhs) (succeed? recheck-rhs))
        (values succeed succeed)] ;TODO can just some of the children vouch in a disj?
       [else (vouch rdcee e-normalized r-normalized (and (succeed? recheck-lhs) (succeed? recheck-rhs)))])))

  (org-define (==-reduce rdcee s e-free r-disjunction e-normalized r-normalized)
    (cert (goal? rdcee) (mini-substitution? s)) ;TODO make == rechecks as needed. non trivial probably => recheck
    (exclusive-cond
     [(==? rdcee) (let-values ([(lhs-normalized? lhs) (mini-walk-normalized s (==-lhs rdcee))]
                           [(rhs-normalized? rhs) (mini-walk-normalized s (==-rhs rdcee))])
                (vouch (== lhs rhs) e-normalized r-normalized (and lhs-normalized? rhs-normalized?)))]
     [(=/=? rdcee) (let-values ([(rdcee r-vouches) (mini-disunify/normalized s (=/=-lhs rdcee) (=/=-rhs rdcee))])
                 (vouch rdcee e-normalized r-normalized r-vouches))]
     ;(reduce-noto rdcee s e-free r-disjunction e-normalized r-normalized)
     [(matcho? rdcee) (let-values ([(expanded? rdcee ==s) (matcho/expand rdcee s)])
                    (if expanded? ;TODO should matcho's ==s/contents be recheck or satisfied?
                        (let-values ([(simplified recheck) (reduce-constraint rdcee s e-free r-disjunction e-normalized r-normalized)])
                          (values (conj ==s simplified) recheck))
                        (simplify (conj ==s rdcee))))]
     [(pconstraint? rdcee) (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized)]
     [(proxy? rdcee) (simplify (if (mini-normalized? s (proxy-var rdcee)) succeed rdcee))] ;TODO does reduce == proxy need to be rechecked?
     [else (assertion-violation '==-reduce "Unrecognized constraint type" rdcee)]))

  (org-define (=/=-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
              ;; =/= can only simplify ==->fail and =/=->succeed
              (cert (=/=? rcdrr))
    (exclusive-cond
     [(==? rdcee) ; -> fail,  ==
      (simplify (let* ([s (=/=->substitution rcdrr)] ; TODO make a pure =/= x =/= system that doesnt have tu fully unify
                       [s^ (mini-unify s (==-lhs rdcee) (==-rhs rdcee))])
                  (if (eq? s s^) fail rdcee)))]
     [(=/=? rdcee) ; -> succeed, =/=
      (cert (not (pair? (=/=-lhs rdcee))))
      (cond
       [(and e-free r-disjunction) (vouch rdcee e-normalized #f #f)] ; If reducer is in a disjunction, and reducee is free, we don't want to do any reducing because we want the reducee to later simplify the reducer an take out the disjunction in the store rather than having the disjunction take out the simpler free =/=
       ;; TODO can unequal =/= cancel? eg can x=/=y and y=/=x both show up in reducer?
       [(equal? rdcee rcdrr) (values succeed succeed)] ; Identical =/= can cancel
       [else ; We can vouch for reducee when it's already normalized, or when reducer is and has all the same vars.
        (vouch rdcee e-normalized r-normalized (vouches (noto-goal rcdrr) (noto-goal rdcee)))])]
     [(or (matcho? rdcee) (pconstraint? rdcee)) (simplify rdcee)]
     [(proxy? rdcee) (if (or (eq? (=/=-lhs rcdrr)  (proxy-var rdcee)) (eq? (=/=-rhs rcdrr)  (proxy-var rdcee))) (values succeed succeed) (check rdcee))]
     [else (assertion-violation '=/=-reduce "Unrecognized constraint type" rdcee)]))
  
  (define (pconstraint-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (cert (pconstraint? rcdrr))
    (exclusive-cond
     [(==? rdcee) (let-values ([(simplified recheck) (==/pconstraint-reduce rcdrr (==->substitution rdcee) e-free r-disjunction e-normalized r-normalized)])
                (if (fail? simplified) (values fail fail) (simplify rdcee)))]
     [(=/=? rdcee) ; -> succeed, =/=
      (let-values ([(simplified recheck) (==/pconstraint-reduce rcdrr (=/=->substitution rdcee) e-free r-disjunction e-normalized r-normalized)])
        (if (fail? simplified) (values succeed succeed) (simplify rdcee)))]
     [else (assertion-violation 'pconstraint-reduce "Unrecognized constraint type" rdcee)]))

  (define ==/pconstraint-reduce ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda ;TODO can we reuse this like matcho/expand in solver?
      [(rdcee s e-free r-disjunction e-normalized r-normalized) (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized (pconstraint-vars rdcee))]
      [(rdcee s e-free r-disjunction e-normalized r-normalized vars)
       (if (null? vars) (simplify rdcee)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (==/pconstraint-reduce rdcee s e-free r-disjunction e-normalized r-normalized (cdr vars))
                 (reduce-constraint ((pconstraint-procedure rdcee) (car vars) v rdcee succeed rdcee) s e-free r-disjunction e-normalized r-normalized))))]))

  (define (matcho-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(==? rdcee) (if (failure? (mini-unify-substitution (matcho-substitution rcdrr) (==->substitution rdcee))) (values fail fail) (simplify rdcee))]
     [(=/=? rdcee) ; -> succeed, =/=
      (if (failure? (mini-unify-substitution (matcho-substitution rcdrr) (=/=->substitution rdcee)))
          (values succeed succeed) (simplify rdcee))] ;TODO could a =/= of lists simultaneously fail?
     ;;TODO matchos with eq? lambda can cancel
     [else (assertion-violation 'matcho-reduce "Unrecognized constraint type" rdcee)]))

  (define (noto-reduce rdcee rcdrr e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint rcdrr (if (noto? rdcee) (noto rdcee) rdcee) e-free r-disjunction e-normalized r-normalized)])
      (if (and (succeed? simplified) (succeed? recheck))
          (if (noto? rdcee) (values succeed succeed) (values fail fail))
          (simplify rdcee))))

  )
