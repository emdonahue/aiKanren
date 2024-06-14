;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho))
  ;; TODO test whether we need 2 var eq with: x == y | ... AND y == z (or z == y) | ... AND x=/=z

  (define (==->substitution g)
    (cert (==? g) (var? (==-lhs g)))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (=/=->substitution g) ; To fully reduce =/=, we must unroll possibly list disequalities the disunifier lazily ignored.
    (cert (=/=? g)) 
    (mini-unify '() (=/=-lhs g) (=/=-rhs g)))

  (define (vouch e e-normalized r-normalized r)
    (if (fail? e) (values fail fail)
        (if (or e-normalized (and r-normalized (vouches? r e))) (values e succeed) (values succeed e))))
  
  (define (vouches? r e)
    (cert (or (goal? r) (mini-substitution? r)) (goal? e))
    (or (succeed? r)
     (if (mini-substitution? r)
         (for-all (lambda (v) (mini-normalized? r v)) (normalized-vars e))
         (let ([n-vars (normalized-vars r)])
           (for-all (lambda (v) (member v n-vars)) (normalized-vars e))))))
  
  
  ;; === REDUCEE ===
  (define reduce-constraint
    ;; Reduce existing constraint g using new constraint c.
    ;; e-free => g is a e-free constraint (not in the store). for a e-free =/=, this means that =/= in the store won't simplify it away, so that we can turn around and use it to simplify the =/= already in the story, which may in turn simplify containing disj. e-free mode preserves some information. #f=store mode goes all out to simplify the store.
    (case-lambda
      [(e r e-free) (reduce-constraint e r e-free #f e-free (not e-free))]
      [(e r e-free r-disjunction e-normalized r-normalized)
       (cert (goal? e) (or (fail? e) (not (fail? r))) (or (goal? r) (mini-substitution? r))) ; -> simplified recheck
       (if (succeed? r) (values e succeed) ; Succeed can only be a sole store constraint, so we know e is normalized
           (exclusive-cond
            [(or (fail? e) (succeed? e)) (values e e)]
            [(conj? e) (reduce-conj e r e-free r-disjunction e-normalized r-normalized)]
            [(disj? e) (reduce-disj e r e-free r-disjunction e-normalized r-normalized)]
            [(and (noto? e) (not (=/=? e))) (reduce-noto e r e-free r-disjunction e-normalized r-normalized)]
            [(constraint? e) (reduce-constraint (constraint-goal e) r e-free r-disjunction e-normalized r-normalized)]
            [(and (=/=? e) (pair? (=/=-lhs e)))
             (reduce-constraint (mini-disunify '() (=/=-lhs e) (=/=-rhs e)) r e-free r-disjunction e-normalized r-normalized)]
            [(proxy? e) (constraint-reduce e r #f r-disjunction #f r-normalized)] ; Proxies are never normalized bc they can't be stored. They can only be rechecked. They are also never free.
            [else (constraint-reduce e r e-free r-disjunction e-normalized r-normalized)]))]))
  
  (define (reduce-conj e r e-free r-disjunction e-normalized r-normalized)
    (cert (conj? e))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs e) r e-free r-disjunction e-normalized r-normalized)])
      (if (fail? simplified-lhs) (values fail fail)
          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs e) r e-free r-disjunction e-normalized r-normalized)])
            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs))))))

  (org-define (reduce-disj e r e-free r-disjunction e-normalized r-normalized)
              (cert (disj? e))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs e) r e-free r-disjunction e-normalized r-normalized)])
      (exclusive-cond
       [(and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)]
       [(fail? simplified-lhs) (reduce-constraint (disj-rhs e) r e-free r-disjunction #f r-normalized)]
       [else
        (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs e) r e-free r-disjunction #f r-normalized)])
          (vouch (disj (conj simplified-lhs recheck-lhs) (conj simplified-rhs recheck-rhs))
                 e-normalized (and r-normalized (succeed? recheck-lhs)) succeed))])))
  
  (define (reduce-noto e r e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal e) r e-free r-disjunction e-normalized r-normalized)])
      (vouch (disj (noto simplified) (noto recheck)) e-normalized (and r-normalized (succeed? recheck)) succeed)))

  ;; === REDUCER ===
  (define (constraint-reduce e r e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(list? r) (==-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(==? r) (==-reduce e (==->substitution r) e-free r-disjunction e-normalized r-normalized)]
     [(=/=? r) (=/=-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(pconstraint? r) (pconstraint-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(conj? r) (conj-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(disj? r) (disj-reduce e r e-free e-normalized r-normalized)]
     [(noto? r) (noto-reduce e (noto-goal r) e-free r-disjunction e-normalized r-normalized)]
     [(matcho? r) (matcho-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(proxy? r) (vouch e e-normalized #f succeed)] ; Proxies are never normalized and so can vouch for nothing
     [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons e r))]))
  
  (define (conj-reduce e r e-free r-disjunction e-normalized r-normalized)
    (let*-values ([(simplified recheck) (reduce-constraint e (conj-lhs r) e-free r-disjunction e-normalized r-normalized)]
                  [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs r) e-free r-disjunction e-normalized r-normalized)]
                  [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs r) e-free r-disjunction e-normalized r-normalized)])
      (values (conj simplified/simplified (conj simplified/recheck recheck/simplified)) recheck/recheck)))
  
  (org-define (disj-reduce e r e-free e-normalized r-normalized)
              (cert (disj? r))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint e (disj-lhs r) e-free #t e-normalized r-normalized)]
                 [(simplified-rhs recheck-rhs) (reduce-constraint e (disj-rhs r) e-free #t e-normalized #f)])
      (org-cond
       [(fail? simplified-lhs) (values simplified-rhs recheck-rhs)]
       [(fail? simplified-rhs) (values simplified-lhs recheck-lhs)]
       [(and (succeed? simplified-lhs) (succeed? simplified-rhs) (succeed? recheck-lhs) (succeed? recheck-rhs))
        (values succeed succeed)]
       [else (vouch e e-normalized (and r-normalized (or (and (succeed? recheck-lhs) (not (succeed? simplified-lhs)))
                                                           (and (succeed? recheck-rhs) (not (succeed? simplified-rhs))))) succeed)])))

  (org-define (==-reduce e s e-free r-disjunction e-normalized r-normalized)
    (cert (goal? e) (mini-substitution? s))
    (exclusive-cond
     [(==? e) (let-values ([(lhs-normalized? lhs) (mini-walk-normalized s (==-lhs e))]
                               [(rhs-normalized? rhs) (mini-walk-normalized s (==-rhs e))])
                    (vouch (== lhs rhs) e-normalized (and r-normalized (var? lhs) lhs-normalized? rhs-normalized?) succeed))]
     [(=/=? e) (let-values ([(e r-vouches) (mini-disunify/normalized s (=/=-lhs e) (=/=-rhs e))])
                 (vouch e e-normalized (and r-normalized r-vouches) succeed))]
     [(matcho? e) (let-values ([(expanded? e ==s) (matcho/expand e s)])
                    (if expanded?
                        (reduce-constraint (conj ==s e) s e-free r-disjunction #f r-normalized)
                        (let-values ([(==s ==s/recheck) (reduce-constraint ==s s e-free r-disjunction #f r-normalized)]
                                     [(e e/recheck) (vouch e e-normalized r-normalized s)])
                          (values (conj ==s e) (conj ==s/recheck e/recheck)))))]
     [(pconstraint? e) (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized)]
     [(proxy? e) ; If we can vouch that they have already been walked, discard. Otherwise we have to walk them (cant be stored). 
      (if (and r-normalized (mini-normalized? s (proxy-var e))) (values succeed succeed) (values succeed e))] 
     [else (assertion-violation '==-reduce "Unrecognized constraint type" e)]))

  (org-define (=/=-reduce e r e-free r-disjunction e-normalized r-normalized)
              ;; =/= can only simplify ==->fail and =/=->succeed
              (cert (=/=? r))
    (exclusive-cond
     [(==? e) ; -> fail?. Simple equality check ok because 1) we ignore list unifications for performance reasons, constants will already succeed or fail, and == orders vars by id
      (vouch (if (equal? e (noto-goal r)) fail e) e-normalized r-normalized (noto-goal r))]
     [(=/=? e) ; -> succeed, =/=
      (cert (not (pair? (=/=-lhs e))))
      (if (and (not (and e-free r-disjunction)) (equal? e r)) ; If reducee is free and reducer is in a disjunction, we must negate our usual symmetric equality check and preserve the reducee so it can later simplify the reducer.
          (values succeed succeed) ; Identical =/= can cancel
          (vouch e e-normalized (and r-normalized (not (and e-free r-disjunction))) (noto-goal r)))]
     [(matcho? e) (vouch e e-normalized r-normalized r)]
     [(pconstraint? e) (vouch e e-normalized r-normalized r)]
     [(proxy? e) (if (vouches? r e) (values succeed succeed) (values succeed e))]
     [else (assertion-violation '=/=-reduce "Unrecognized constraint type" e)]))
  
  (define (pconstraint-reduce e r e-free r-disjunction e-normalized r-normalized)
    (cert (pconstraint? r))
    (exclusive-cond
     [(==? e) (let-values ([(simplified recheck) (==/pconstraint-reduce r (==->substitution e) e-free r-disjunction e-normalized r-normalized)])
                (if (fail? simplified) (values fail fail) (vouch e e-normalized r-normalized r)))]
     [(=/=? e) ; -> succeed, =/=
      (let-values ([(simplified recheck) (==/pconstraint-reduce r (=/=->substitution e) e-free r-disjunction e-normalized r-normalized)])
        (if (fail? simplified) (values succeed succeed) (vouch e e-normalized r-normalized r)))]
     [else (assertion-violation 'pconstraint-reduce "Unrecognized constraint type" e)]))

  (define ==/pconstraint-reduce ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda 
      [(e s e-free r-disjunction e-normalized r-normalized) (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized (pconstraint-vars e))]
      [(e s e-free r-disjunction e-normalized r-normalized vars)
       (if (null? vars) (vouch e e-normalized r-normalized succeed)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized (cdr vars))
                 (reduce-constraint ((pconstraint-procedure e) (car vars) v e succeed e) s e-free r-disjunction e-normalized r-normalized))))]))

  (org-define (matcho-reduce e r e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(==? e) (if (failure? (mini-unify (matcho-substitution r) (==-lhs e) (==-rhs e)))
                      (values fail fail)
                      (vouch e e-normalized r-normalized r))]
     [(=/=? e) ; -> succeed, =/=
      (let-values ([(d n?) (mini-disunify/normalized (matcho-substitution r) (=/=-lhs e) (=/=-rhs e))])
        (org-display d n? (matcho-substitution r) e)
        (if (succeed? d) (values succeed succeed) (vouch e e-normalized r-normalized r)))]
     ;;TODO matchos with eq? lambda can cancel
     [else (assertion-violation 'matcho-reduce "Unrecognized constraint type" e)]))

  (define (noto-reduce e r e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint r (if (noto? e) (noto-goal e) e) e-free r-disjunction e-normalized r-normalized)])
      (if (and (succeed? simplified) (succeed? recheck))
          (if (noto? e) (values succeed succeed) (values fail fail))
          (vouch e e-normalized r-normalized r)))))
