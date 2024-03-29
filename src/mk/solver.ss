(library (solver) ; Central logic of the constraint solver
  (export run-constraint simplify-=/= simplify-pconstraint)
  (import (chezscheme) (state) (negation) (goals) (streams) (variables) (utils) (debugging) (mini-substitution) (reducer) (matcho))

  (org-define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
              (cert (goal? g) (maybe-state? s)) ; -> maybe-state?
    (let-values ([(delta s) (solve-constraint g s succeed succeed succeed)]) s))

  (org-define (solve-constraint g s ctn resolve delta)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    ;; resolve: constraints retrieved from the store that we need to recheck, but which should not be negated by noto on the return (so we cant just solve them immediately. we must delay rechecking until we are done with g).
    ;; delta: conjunction of all the simplified goals we have added to the store. reflects the change (delta) of the returned state's constraint store.
    (cert (goal? g) (maybe-state? s) (goal? ctn)) ; -> delta maybe-state?
    (if (failure? s) (values fail failure)
        (exclusive-cond
         [(fail? g) (values fail failure)]
         [(succeed? g) (solve-succeed s ctn resolve delta)]
         [(==? g) (solve-== g s ctn resolve delta)]
         [(noto? g) (solve-noto (noto-goal g) s ctn resolve delta)]
         [(disj? g) (solve-disj g s ctn resolve delta)]
         [(conde? g) (solve-constraint (conde->disj g) s ctn resolve delta)]
         [(conj? g) (solve-constraint (conj-lhs g) s (conj (conj-rhs g) ctn) resolve delta)]
         [(constraint? g) (solve-constraint (constraint-goal g) s ctn resolve delta)]
         [(suspend? g) (solve-constraint (suspend-goal g) s ctn resolve delta)]
         [(matcho? g) (solve-matcho g s ctn resolve delta)]
         [(matcho4? g) (solve-matcho2 g s ctn resolve delta)]
         [(pconstraint? g) (solve-pconstraint g s ctn resolve delta)]
         [(proxy? g) (solve-proxy g s ctn resolve delta)]
         [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)])))


  (org-define (solve-succeed s ctn resolve delta)
    (if (succeed? ctn) ; Solve until continuation is trivial.
        (if (succeed? resolve) ; If we have no ctn and nothing left to recheck, we're done.
            (values delta s)
            (let-values ([(resolved s) (solve-constraint resolve s succeed succeed delta)])
              (values (if (fail? resolved) fail delta) s))) ; If our recheck constraints fail, fail. Otherwise return the delta of the original simplified constraint (not the rechecks, since we don't want noto to negate the rechecked values that were removed from the constraint store but that were not children of noto). We want to make sure all constraints succeed, but we only want to save the simplified form of our original constraint. Not others that must be rechecked as a result of checking it (eg because it is a unification that fires subsequent constraints).
        (solve-constraint ctn s succeed resolve delta)))

  (define (solve-disj g s ctn resolve delta)
    (let-values ([(d-lhs s-lhs) (solve-constraint (disj-lhs g) s succeed succeed succeed)]) ; Solve the lhs in a new hypothetical environment with no continuation. Just simplify the current disj goals in the context of the current state. Passing the continuation through creates many copies of the same constraints, which destroys performance.
      (exclusive-cond ; Solve the lhs disjunct.
       [(fail? d-lhs) (solve-constraint (disj-rhs g) s ctn resolve delta)] ; If it fails, continue solving disjuncts.
       [(succeed? d-lhs) (solve-constraint ctn s succeed resolve delta)] ; If it succeeds, discard the entire disj constraint.
       [else ; If it only simplifies, store the simplified disj with a new lhs.
        (let ([simplified-lhs (disj d-lhs (disj-rhs g))])
          (solve-constraint ctn (store-constraint s simplified-lhs)
                            succeed resolve (conj delta simplified-lhs)))])))

  (define (solve-matcho g s ctn resolve delta) 
    (let-values ([(g s expanded?) (solve-matcho/expand g s)])
      (if expanded?
          (solve-constraint g s ctn resolve delta)
          (solve-constraint ctn (store-constraint s g) succeed resolve (conj delta g)))))

  (define (solve-matcho/expand g s)
    ;; Simplify matcho using s, but do not solve the contained constraint if matcho simplifies completely.
    (cert (goal? g) (state? s)) ; -> constraint? state? simplified-completely?
    (if (null? (matcho-out-vars g)) ; If all external variables have been assigned ground values,
        (let-values ([(_ g s p) (expand-matcho g s empty-package)]) ; expand the inner goal procedure.
          (values g s #t)) ; Otherwise walk the first external var in the current state.
        (let ([v (walk-var s (car (matcho-out-vars g)))]) ;TODO replace walkvar in matcho solver with walk once matcho handles walks
          (if (var? v) ; If it is free, continue to suspend matcho. Otherwise, continue walking variables.
              (values (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g)) s #f)
              (solve-matcho/expand (make-matcho (cdr (matcho-out-vars g)) (cons v (matcho-in-vars g)) (matcho-goal g)) s)))))

  (org-define (solve-matcho2 g s ctn resolve delta)
    (let-values ([(expanded? g ==s) (solve-matcho2/expand g s)])
      (if expanded?
          (solve-constraint g s (conj ==s ctn) resolve delta)
          (solve-constraint (conj ==s ctn) (store-constraint s g) succeed resolve (conj delta g)))))
  
  (define solve-matcho2/expand
    (org-case-lambda matcho/expand
      [(g s) (solve-matcho2/expand g s succeed '())]
      [(g s ==s walked)
       (let ([w (find (lambda (v) (not (memq v walked))) (matcho4-vars g))]) ; Find the next variable we haven't walked.
         (if w (let ([v (walk-var s w)]) ; If there is an unwalked variable, walk it.
                 (if (var? v) ; If it is a var, swap it out and continue expanding.
                     (solve-matcho2/expand
                      (make-matcho4 (map (lambda (x) (if (eq? w x) v x)) (matcho4-vars g))
                                    (matcho4-procedure g))
                      s ==s (cons w walked)) 
                     (let-values ([(expanded? shared match) ; Otherwise run the matcher.
                                   (apply (matcho4-procedure g) ; Replace the unwalked var with its walked value.
                                          (map (lambda (x) (if (eq? w x) v x)) (matcho4-vars g)))]) 
                       (if expanded? ; If the constraint is fully expanded, return. Else continue expanding.
                           (values #t match (conj ==s shared))
                           (solve-matcho2/expand match s (conj ==s shared) (cons w walked))))))
             ;; If we've walked them all and the constraint is still unsolved, store the constraint continue solving.
             (values #f g ==s)))]))
  
  (define (solve-proxy g s ctn resolve delta) ; Solves the constraint on the proxied varid.
    (let-values ([(v c) (walk-var-val s (proxy-var g))])
      (if (goal? c) (solve-constraint c (extend s v succeed) ctn resolve delta)
          (solve-constraint ctn s succeed resolve delta))))

  (org-define (solve-noto g s ctn resolve delta)
    (cert (not (noto? g))) ; g is the already unwrapped inner goal of the noto.
    (exclusive-cond
     [(==? g) (solve-=/= g s ctn resolve delta)]
     [(matcho? g) ; Because matcho may return a negatable complex constraint (like disj), we must expand it and see if we can perform the negation before we know how to solve the resulting constraint. Otherwise eg we might solve only 1 branch of a disj, but then attempt to store all branches of a conj into the state, though some branches may contain stale variables.
      (let-values ([(g s^ expanded?) (solve-matcho/expand g s)])
        (let ([s (if (failure? s^) s s^)]) ; Negating a failure gives a success, but since we cant invert a failure s^ directly, we return the previous s as its inversion.
          (if expanded?
              (solve-constraint (noto g) s ctn resolve delta)
              (solve-constraint ctn (store-constraint s (noto g)) succeed resolve (conj delta (noto g))))))]
     [(matcho4? g) ; Because matcho may return a negatable complex constraint (like disj), we must expand it and see if we can perform the negation before we know how to solve the resulting constraint. Otherwise eg we might solve only 1 branch of a disj, but then attempt to store all branches of a conj into the state, though some branches may contain stale variables.
      (let-values ([(expanded? g ==s) (solve-matcho2/expand g s)])
        (let ([g (disj (noto ==s) (noto g))])
         (if expanded?
             (solve-constraint g s ctn resolve delta)
             (solve-constraint ctn (store-constraint s g) succeed resolve (conj delta g)))))]
     [else
      (let-values ([(g s^) ; Evaluate the positive constraint hypothetically and invert the result (success <=> failure). Discard the state, which may have changed under the hypothetical positive constraint, and keep only the simplified constraint g, which we negate and return to the store. This is the same logic as for classical implementations of disequality (inverting the substitution of unification), but generalized to arbitrary constraints.
                    (solve-constraint g s succeed succeed succeed)])
        (solve-constraint ctn (store-constraint s (noto g)) succeed resolve (conj delta (noto g))))]))








  (org-define (solve-== g s ctn resolve delta)
              ;; Runs a unification, collects constraints that need to be rechecked as a result of unification, and solves those constraints.
              ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
              ;; TODO if we only get 1 binding in solve-==, it has already been simplified inside unify and we can skip it
              ;; TODO can we simplify delta/pending as well and simplify already delta constraints from lower in the computation?
              (let-values ([(bindings simplified committed pending delta s) (unify s delta (==-lhs g) (==-rhs g))]) ; bindings is a mini-substitution of normalized ==s added to s. simplified is a constraint that does not need further solving, recheck is a constraint that does need further solving, s is the state
                (if (fail? bindings) (values fail failure)
                    (solve-constraint ctn (store-constraint s simplified) succeed (conj pending (conj resolve committed))
                                      delta))))



  (define (solve-=/= g s ctn resolve delta)
    ;; Solves a =/= constraint lazily by finding the first unsatisfied unification and suspending the rest of the unifications as disjunction with a list =/=.
    (cert (==? g)) ; -> delta state?
    (let-values ([(g c) (disunify s (==-lhs g) (==-rhs g))]) ; g is normalized x=/=y, c is constraints on x&y that need to be rechecked
      (if (or (succeed? g) (fail? g)) (solve-constraint g s ctn resolve delta) ; If g is trivially satisfied or unsatisfiable, skip the rest and continue with ctn.
          (if (disj? g) (solve-constraint g s ctn resolve delta) ; TODO add flag to let solve-disj know that its constraint might be normalized and to skip initial solving
              (let-values ([(unified disunified recheck diseq) (simplify-=/= c (=/=-lhs g) (=/=-rhs g) g)]) ; Simplify the constraints with the first disjoined =/=.
                                        ;(org-display unified disunified recheck diseq)
                (if (succeed? unified) (solve-constraint ctn s succeed resolve delta) ; If the constraints entail =/=, skip the rest and continue with ctn.
                    (solve-constraint ctn (store-constraint (extend s (=/=-lhs g) disunified) diseq) succeed (conj recheck resolve) (conj delta g))))))))

  (define (simplify-=/= g x y d)
    ;; Simplifies the constraint g given the new constraint x=/=y. Simultaneously constructs 4 goals:
    ;; 1) g simplified under the assumption x==y. If fail?, g => x=/=y, so we can simply throw away the new constraint. Since we only need to check for failure, we can cut corners and not compute the true simplification of g, g', so long as ~g <=> ~g'.
    ;; 2) g simplified under x=/=y but only conjuncts that are completely normalized. Since they are guaranteed to be already normalized, we can simply add them directly to the store.
    ;; 3) g simplified under x=/=y, but only conjuncts that might be unnormalized. We must re-check these with the full solver.
    ;; 4) The final disequality constraint x=/=y. If it is already entailed by our simplifications of g, just return succeed. This will be conjoined to the constraint from #2 when adding to the store.
    (cert (goal? g)) ; -> goal?(unified) goal?(disunified) goal?(recheck) goal?(disequality)
    (exclusive-cond
     [(succeed? g) (values fail succeed succeed d)] ; If no constraints on x, add succeed back to the store.
     [(==? g) (let* ([s (if (eq? (==-lhs g) x) '() (list (cons (==-lhs g) (==-rhs g))))]
                     [s^ (if (eq? (==-lhs g) x) (mini-unify '() (==-rhs g) y) (mini-unify s x y))]) ;TODO is mini-unify necessary in solve-disj since the constraints should be normalized so we don't have two pairs?
                (let-values ([(simplified recheck) (reduce-constraint g (== x y) `((,x . ,y)))])
                  (exclusive-cond ; unification necessary in case of free vars that might be unified but are not equal, such as (<1> . <2>) == (<2> . <1>)
                   [(failure? s^) (values succeed g succeed d)] ; == different from =/= => =/= satisfied
                   [(eq? s s^) (values fail fail succeed d)] ; == same as =/= => =/= unsatisfiable
                   [else (values g g succeed d)])))] ; free vars => =/= undecidable
     [(pconstraint? g) (if (pconstraint-attributed? g x) (values (noto (pconstraint-check g x y)) g succeed d) (values g g succeed d))] ; The unified term succeeds or fails with the pconstraint. The disunified term simply preserves the pconstraint.
     [(matcho? g) (if (and (matcho-attributed? g x) (not (or (var? y) (pair? y)))) (values succeed g succeed d) ; Check that y could be a pair.
                      (values g g succeed d))] ;TODO add patterns to matcho and check them in simplify-=/=
     [(noto? g) (let-values ([(unified disunified recheck d) (simplify-=/= (noto-goal g) x y d)]) ; Cannot contain disjunctions so no need to inspect returns.
                  (cert (succeed? recheck)) ; noto only wraps primitive goals since its a =/=, which should never need rechecking on their own
                  (values (noto unified) (noto disunified) recheck d))]

     ;; if =/= in a conj => skip
     ;; if =/= in a disj => dont skip
     ;; if =/= not in a disj, ski ok
     ;; cant be in both conj and disj??
     [(conj? g) (let-values ([(unified disunified-lhs recheck-lhs d) (simplify-=/= (conj-lhs g) x y d)])
                  (if (succeed? unified) (values succeed disunified-lhs recheck-lhs d) ; If unified fails, we can throw the =/= away, so abort early.
                      (let-values ([(unified disunified-rhs recheck-rhs d) (simplify-=/= (conj-rhs g) x y d)])
                        (values unified (conj disunified-lhs disunified-rhs) (conj recheck-lhs recheck-rhs) d))))]
     [(disj? g) (simplify-=/=-disj g x y d)]
     [(fail? g) (values succeed fail fail fail)] ; Empty disjunction tail. Fail is thrown away by disj.
     [(constraint? g) (simplify-=/= (constraint-goal g) x y d)]
     [(procedure? g) (nyi simplify-=/= proceedure)]
     [(proxy? g) (values g succeed g d)] ;TODO can we discard proxies in some cases while reducing =/=?
     [else (assertion-violation 'simplify-=/= "Unrecognized constraint type" g)]))

  (define (simplify-=/=-disj g x y d)
    (let*-values ([(unified-lhs simplified-lhs recheck-lhs d)
                   (simplify-=/= (disj-lhs g) x y d)]
                  [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
      (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d)
          (let*-values ([(unified-rhs simplified-rhs recheck-rhs d)
                         (simplify-=/= (disj-rhs g) x y d)]
                        [(disunified-rhs) (conj simplified-rhs recheck-rhs)])
            (if (succeed? disunified-rhs) (values unified-rhs succeed succeed d)
                (let ([unified (conj unified-lhs unified-rhs)])
                  (let-values ([(conjs disjs lhs rhs) (disj-factorize disunified-lhs disunified-rhs)])
                    (let ([disunified
                           (conj conjs (conj
                                        (if (not (or (succeed? unified-lhs) (succeed? unified-rhs)))
                                            (conj d (disj lhs rhs))
                                            (disj (if (succeed? unified-lhs) lhs (conj d lhs))
                                                  (if (succeed? unified-rhs) rhs (conj d rhs)))) disjs))])
                      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
                              (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                   (conj-memp simplified-lhs ==?)))
                          (values unified succeed disunified succeed)
                          (values unified disunified succeed succeed))))))))))



  (define solve-pconstraint
    (case-lambda
      [(g s ctn resolve delta) (solve-pconstraint g s ctn resolve delta '())]
      [(g s ctn resolve delta vs) ; -> delta pending state?
       (cert (goal? g) (state? s) (goal? ctn) (goal? resolve) (goal? delta) (list? vs))
       (if (not (pconstraint? g)) (solve-constraint g s ctn resolve delta)
           (let ([var (find (lambda (v) (not (memq v vs))) (pconstraint-vars g))])
             (if (not var) (solve-constraint ctn (store-constraint s g) succeed resolve (conj delta g)) ; All vars walked. Store constraint.
                 (let-values ([(var^ val) (walk-var-val s var)])
                   (let ([vs (cons var^ vs)])
                     (cond
                      [(var? val) (solve-pconstraint (pconstraint-rebind-var g var val) s ctn resolve delta vs)] ; Assume for the moment that pconstraints only operate on ground values, so we can simply replace var-var bindings. Identical free vars can always be skipped.
                      [(goal? val) (let-values ([(g simplified recheck p)
                                                 (simplify-pconstraint val (pconstraint-rebind-var g var var^))])
                                     (if (succeed? g) (solve-constraint ctn s succeed resolve delta)
                                         (if (or (fail? simplified) (fail? recheck)) (values fail failure)
                                             (solve-pconstraint g (extend s var^ simplified) ;TODO can we just stash the pconstraint with the simplified under certain conditions if we know it wont need further solving?
                                                                ctn (conj recheck resolve) delta vs))))]
                      [else (solve-pconstraint (pconstraint-check g var^ val) s ctn resolve delta vs)]))))))]))

  (define simplify-pconstraint
    (case-lambda
      [(g p) (simplify-pconstraint g p p)]
      [(g p c)
       (cert (or (pconstraint? p) (succeed? p)) (goal? g) (or (succeed? c) (pconstraint? c)))
       (cond
        [(succeed? p) (values succeed succeed succeed c)]
        [(conj? g) (let-values ([(p-lhs simplified-lhs recheck-lhs c) (simplify-pconstraint (conj-lhs g) p c)])
                     (if (or (fail? p-lhs) (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail succeed c)
                         (let-values ([(p-rhs simplified-rhs recheck-rhs c) (simplify-pconstraint (conj-rhs g) p c)])
                           (values (if (or (succeed? p-lhs) (succeed? p-rhs)) succeed p) (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs) c))))]
        [(disj? g) (simplify-pconstraint-disj g p c)]
        [(pconstraint? g) (if (equal? p g) (values succeed succeed succeed c)
                              (let ([v (memp (lambda (v) (memq v (pconstraint-vars g))) (pconstraint-vars p))])
                                (if (not v) (values p g succeed c)
                                    (let-values ([(g simplified recheck) ((pconstraint-procedure g) v v p g p)])
                                      (values g simplified recheck c)))))]
        [(==? g) (if (memq (==-lhs g) (pconstraint-vars p))
                     (let ([entailed ((pconstraint-procedure p) (==-lhs g) (==-rhs g) p succeed p)])
                       (values entailed (if (fail? entailed) fail g) succeed c))
                     (values p g succeed c))
         #;
         (let-values ([(simplified recheck) (simplify-unification p (->mini-substitution g))]) ;
         (values simplified g recheck c))]
        ;; numbero & not numbero -> succeed succeed -> fail fail
        ;; numbero & not symbolo  -> fail fail -> numbero succeed
        ;; numbero & =/=1 -> succeed ==1 -> numbero =/=1
        ;; numbero & =/='symbol -> fail fail -> numbero succeed
        ;; numbero & not symbolo x2 -> numbero symbolo x2 -> numbero not symbolo x2
        [(noto? g) (let-values ([(entailed simplified recheck c) (simplify-pconstraint (noto-goal g) p c)])
                     (org-display entailed simplified recheck)
                     (when (not (succeed? recheck)) (display p))
                     (cert (succeed? recheck))
                     (let ([p (if (and (succeed? entailed) (succeed? simplified)) fail p)])
                       (values p (noto simplified) succeed c)))]
        [(matcho? g) (let ([v (memp (lambda (v) (memq v (matcho-out-vars g))) (pconstraint-vars p))])
                       (if (not v) (values p g succeed c)
                           (let-values ([(entailed simplified recheck) ((pconstraint-procedure p) v v p g p)])
                             (values entailed simplified recheck c))))]
        [else (values p g succeed c)])]))

  (define (simplify-pconstraint-disj g p d)
    (cert (or (succeed? d) (pconstraint? d)))
    (let*-values ([(unified-lhs simplified-lhs recheck-lhs d)
                   (simplify-pconstraint (disj-lhs g) p d)]
                  [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
      (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d)
          (let*-values ([(unified-rhs simplified-rhs recheck-rhs d)
                         (simplify-pconstraint (disj-rhs g) p d)]
                        [(disunified-rhs) (conj simplified-rhs recheck-rhs)])
            (if (succeed? disunified-rhs) (values unified-rhs succeed succeed d)
                (let ([unified (if (and (succeed? unified-lhs) (succeed? unified-rhs)) succeed p)])
                  (let-values ([(conjs disjs lhs rhs) (disj-factorize disunified-lhs disunified-rhs)])
                                        ;(org-display unified-lhs unified-rhs simplified-rhs lhs rhs d)
                    (let ([disunified
                           (conj conjs (conj
                                        (if (not (or (succeed? unified-lhs) (succeed? unified-rhs)))
                                            (conj d (disj lhs rhs))
                                            (disj (if (succeed? unified-lhs) lhs (conj d lhs))
                                                  (if (succeed? unified-rhs) rhs (conj d rhs)))) disjs))])
                                        ;(org-display unified unified-lhs unified-rhs)
                      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
                              (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                   (conj-memp simplified-lhs ==?))) ; Only need to check simplified since any non succeed recheck will force a recheck
                          (values unified succeed disunified succeed)
                          (values unified disunified succeed succeed))))))))))



  (define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (cert (maybe-state? s) (goal? g) (not (conde? g))) ; -> state?
    (exclusive-cond
     [(fail? g) failure]
     [(succeed? g) s]
     [(conj? g) (store-constraint (store-constraint s (conj-lhs g)) (conj-rhs g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
     [(==? g) (extend s (==-lhs g) (==-rhs g))]
     [else ; All other constraints get assigned to their attributed variables.
      (state-add-constraint s g (list-sort (lambda (v1 v2) (fx< (var-id v1) (var-id v2))) (attributed-vars g)))]))

  (define attributed-vars
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (case-lambda ;TODO create a defrel that encodes context information about what vars were available for use in reasoning about which freshes might be able to unify them within their lexical scope
      [(g) (let-values ([(vs unifies) (attributed-vars g '() #f)]) vs)]
      [(g vs unifies)
       (cert (goal? g))
       (exclusive-cond
        [(succeed? g) (values vs unifies)]
        [(disj? g) (attributed-vars (disj-car g) vs unifies)]
        [(conj? g) (call-with-values
                       (lambda () (attributed-vars (conj-rhs g) vs unifies))
                     (lambda (vs unifies) (attributed-vars (conj-lhs g) vs unifies)))]
        [(noto? g)
         (if (==? (noto-goal g))
             (let ([vs (if (and (var? (==-rhs (noto-goal g))) (not (memq (==-rhs (noto-goal g)) vs))) (cons (==-rhs (noto-goal g)) vs) vs)])
               (let-values ([(vars _) (attributed-vars (noto-goal g) vs #f)])
                 (values vars unifies)))
             (let-values ([(vars _) (attributed-vars (noto-goal g) vs #f)])
               (values vars unifies)))]
        [(==? g) ;TODO test whether == must attribute to both vars like =/=
         (cert (var? (==-lhs g)))
         (values (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs)) #t)]
        [(matcho? g)
         (values (if (or (null? (matcho-out-vars g)) (memq (car (matcho-out-vars g)) vs)) vs (cons (car (matcho-out-vars g)) vs)) unifies)]
        [(matcho4? g)
         (values (matcho4-vars g) unifies)]
        [(pconstraint? g)
         (values (fold-left (lambda (vs v) (if (memq v vs) vs (cons v vs))) vs (pconstraint-vars g)) unifies)]
        [(constraint? g) (attributed-vars (constraint-goal g) vs unifies)]
        [else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])])))
