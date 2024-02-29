(library (solver) ; Central logic of the constraint solver
  (export run-constraint simplify-=/= simplify-pconstraint)
  (import (chezscheme) (state) (negation) (datatypes) (utils) (debugging) (mini-substitution) (reducer))

  (org-define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
    (cert (goal? g) (state-or-failure? s)) ; -> state-or-failure?
    (let-values ([(delta resolved s) (solve-constraint g s succeed succeed succeed)]) s))

  (org-define (solve-constraint g s ctn resolve delta)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    (cert (goal? g) (state-or-failure? s) (goal? ctn)) ; -> delta pending state-or-failure?
    (if (failure? s) (values fail fail failure)
        (exclusive-cond
         [(fail? g) (values fail fail failure)]
         [(succeed? g) (if (succeed? ctn)
                           (if (succeed? resolve)
                               (values delta succeed s)
                               (let-values ([(resolved re-resolved s) (solve-constraint resolve s succeed succeed delta)])
                                 (if (failure? s) (values fail fail failure)
                                     (values delta (conj resolved re-resolved) s)))) ; resolve returns delta, not d, because noto must negate the returned constraint, which must not include constraints from elsewhere in the store
                           (solve-constraint ctn s succeed resolve delta))]
         [(==? g) (solve-== g s ctn resolve delta)]
         [(noto? g) (solve-noto (noto-goal g) s ctn resolve delta)]
         [(disj? g) (solve-disj g s ctn resolve delta)]
         [(conde? g) (solve-constraint (conde->disj g) s ctn resolve delta)]
         [(conj? g) (solve-constraint (conj-car g) s (conj (conj-cdr g) ctn) resolve delta)]
         [(constraint? g) (solve-constraint (constraint-goal g) s ctn resolve delta)]
         [(fresh? g) (let-values ([(g s p) (g s empty-package)])
                       (solve-constraint g s ctn resolve delta))]
         [(matcho? g) (solve-matcho g s ctn resolve delta)]
         [(pconstraint? g) (solve-pconstraint g s ctn resolve delta)]
         [(proxy? g) (let-values ([(v c) (walk-var-val s (proxy-var g))])
                       (if (goal? c) (solve-constraint c (extend s v succeed) ctn resolve delta)
                           (solve-constraint succeed s ctn resolve delta)))]
         [(trace-goal? g) (solve-constraint (trace-goal-goal g) s ctn resolve delta)] ;TODO can we remove trace-goal from general solver 
         [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)])))

  (org-define (solve-noto g s ctn resolve delta)
    (exclusive-cond
     [(==? g) (solve-=/= g s ctn resolve delta)]
     [(matcho? g)
      (let-values ([(g s^ expanded?) (presolve-matcho g s)]) ; Presolve never changes s, but may return failure (which noto negates back to s), so ignore returned s^.
        (if expanded?
            (solve-constraint (noto g) s ctn resolve delta)
            (solve-constraint succeed (store-constraint s (noto g)) ctn resolve (conj delta (noto g)))))]
     [else 
      (let-values ([(c _ s^) (solve-constraint g s succeed succeed succeed)])
        (org-display c s^)
        (when (not (or (reify-constraints) (not (conj-memp c matcho?))))
          (printf "c ~s~%g ~s~%" c g))
        (cert (or (reify-constraints) (not (conj-memp c matcho?))))
        (solve-constraint succeed (store-constraint s (noto c)) ctn resolve (conj delta (noto c)))
        #;
        (if (succeed? p) ; If there are no pending constraints, all delta constraints must be fully normalized (non disj) so we can simply store them and continue. ;
        (solve-constraint succeed (store-constraint s (noto c)) ctn resolve (conj delta (noto c)) pending) ;
        (solve-constraint succeed s (conj (disj (noto c) (noto p)) ctn) resolve delta pending)))]))



  (org-define (solve-== g s ctn resolve delta)
    ;; Runs a unification, collects constraints that need to be rechecked as a result of unification, and solves those constraints.
    ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
              ;; TODO if we only get 1 binding in solve-==, it has already been simplified inside unify and we can skip it
              ;; TODO can we simplify delta/pending as well and simplify already delta constraints from lower in the computation?
    (let-values ([(bindings simplified committed pending delta s) (unify s delta (==-lhs g) (==-rhs g))]) ; bindings is a mini-substitution of normalized ==s added to s. simplified is a constraint that does not need further solving, recheck is a constraint that does need further solving, s is the state
      (if (fail? bindings) (values fail fail failure)
          (solve-constraint succeed (store-constraint s simplified) (conj ctn pending) (conj resolve committed)
                            delta)
          ;;(conj delta (fold-left (lambda (c e) (conj c (make-== (car e) (cdr e)))) succeed bindings))
          #;;;TODO revisit simplifying == once all unifications have been made
          (let-values ([(recheck/simplified recheck/recheck) (simplify-unification recheck bindings)])
            (if (or (fail? recheck/simplified) (fail? recheck/recheck)) (values fail failure)
                (let-values ([(ctn/simplified ctn/recheck) (simplify-unification ctn bindings)])
                  ;;(org-display simplified recheck recheck/simplified recheck/recheck ctn ctn/simplified ctn/recheck)
                  (if (or (fail? ctn/simplified) (fail? ctn/recheck)) (values fail failure)                                            
                      (solve-constraint succeed (store-constraint s (conj simplified (conj recheck/simplified ctn/simplified)))
                                        ctn/recheck (conj recheck/recheck resolve)
                                        (conj delta
                                              (fold-left (lambda (c e) (conj c (make-== (car e) (cdr e)))) succeed bindings))))))))))


  (org-define (solve-=/= g s ctn resolve delta)
              ;; Solves a =/= constraint lazily by finding the first unsatisfied unification and suspending the rest of the unifications as disjunction with a list =/=.
              (cert (==? g)) ; -> delta pending state
              (let-values ([(g c) (disunify s (==-lhs g) (==-rhs g))]) ; g is normalized x=/=y, c is constraints on x&y
                (if (or (succeed? g) (fail? g)) (solve-constraint g s ctn resolve delta) ; If g is trivially satisfied or unsatisfiable, skip the rest and continue with ctn.
                    (if (disj? g) (solve-constraint g s ctn resolve delta) ; TODO add flag to let solve-disj know that its constraint might be normalized and to skip initial solving
                        (let-values ([(unified disunified recheck diseq) (simplify-=/= c (=/=-lhs (disj-car g)) (=/=-rhs (disj-car g)) (disj-car g))]) ; Simplify the constraints with the first disjoined =/=.
                          (org-display unified disunified recheck diseq)
                          (if (succeed? unified) (solve-constraint ctn s succeed resolve delta) ; If the constraints entail =/=, skip the rest and continue with ctn.
                              (solve-constraint succeed (store-constraint (extend s (=/=-lhs g) disunified) diseq) ctn (conj recheck resolve) (conj delta g))))))))

  (org-define (simplify-=/= g x y d)
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

  (org-define (solve-matcho g s ctn resolve delta) ;TODO rebase solve-matcho on presolve-matcho
              (if (null? (matcho-out-vars g)) ; Expand matcho immediately if all vars are ground
                  (let-values ([(_ g s p) (expand-matcho g s empty-package)])
                    (solve-constraint g s ctn resolve delta)) ;TODO replace walkvar in matcho solver with walk once matcho handles walks
                  (let ([v (walk-var s (car (matcho-out-vars g)))]) ;TODO this walk should be handled by == when it replaces var with new binding
                    ;;TODO if we get a non pair, we can fail matcho right away without expanding lambda
                    (if (var? v)        ; If first out-var is free,
                        (let ([m (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g))]) ; store the matcho.
                          (solve-constraint ctn (store-constraint s m) succeed resolve (conj delta m))) ; Otherwise, keep looking for a free var.
                        ;;TODO just operate on the list for matcho solving
                        (solve-matcho (make-matcho (cdr (matcho-out-vars g)) (cons v (matcho-in-vars g)) (matcho-goal g)) s ctn resolve delta)))))

  (define (presolve-matcho g s)
    ;; Simplify matcho using s, but do not solve the contained constraint if matcho simplifies completely.
    (cert (goal? g) (state? s)) ; -> constraint? simplified-completely?
    (if (null? (matcho-out-vars g))
        (let-values ([(_ g s p) (expand-matcho g s empty-package)])
         (values g s #t))
        (let ([v (walk-var s (car (matcho-out-vars g)))])
          (if (var? v)
              (values (make-matcho (cons v (cdr (matcho-out-vars g))) (matcho-in-vars g) (matcho-goal g)) s #f)
              (presolve-matcho (make-matcho (cdr (matcho-out-vars g)) (cons v (matcho-in-vars g)) (matcho-goal g)) s)))))

  (org-define (solve-disj g s ctn resolve delta) ;TODO split g in solve-disj into normalized and unnormalized args to let other fns flexibly avoid double solving already normalized constraints
              (let-values ([(d-lhs r-lhs s-lhs) (solve-constraint (disj-lhs g) s succeed succeed succeed)])
                (exclusive-cond
                 [(fail? d-lhs) (solve-constraint (disj-rhs g) s ctn resolve delta)]
                 [(succeed? d-lhs) (solve-constraint succeed s ctn resolve delta)]
                 [else (solve-constraint succeed (store-constraint s (disj d-lhs (disj-rhs g))) ctn resolve (conj delta (disj d-lhs (disj-rhs g))))]
                 #;
                 [else (let-values ([(d-rhs r-rhs s-rhs) (solve-constraint (disj-rhs g) s succeed succeed succeed)])
                         (if (fail? d-rhs) (solve-constraint succeed s-lhs ctn resolve (conj delta d-lhs))
                          (let ([d (disj-factorized d-lhs d-rhs)])
                            (solve-constraint succeed (store-constraint s d) ctn resolve (conj delta d)))))])))

  (define solve-pconstraint
    (org-case-lambda solve-pconstraint
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
                                                        (if (or (fail? simplified) (fail? recheck)) (values fail fail failure)
                                                            (solve-pconstraint g (extend s var^ simplified) ;TODO can we just stash the pconstraint with the simplified under certain conditions if we know it wont need further solving?
                                                                               ctn (conj recheck resolve) delta vs))))]
                                     [else (solve-pconstraint (pconstraint-check g var^ val) s ctn resolve delta vs)]))))))]))

  (define simplify-pconstraint
    (org-case-lambda simplify-pconstraint
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
                                                   (let-values ([(g simplified recheck) ((pconstraint-procedure g) v v p g (pconstraint-data p))])
                                                     (values g simplified recheck c)))))]
                       [(==? g) (if (memq (==-lhs g) (pconstraint-vars p))
                                    (let ([entailed ((pconstraint-procedure p) (==-lhs g) (==-rhs g) p succeed (pconstraint-data p))])
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
                                          (let-values ([(entailed simplified recheck) ((pconstraint-procedure p) v v p g (pconstraint-data p))])
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
                    (org-display unified-lhs unified-rhs simplified-rhs lhs rhs d)
                    (let ([disunified
                           (conj conjs (conj
                                        (if (not (or (succeed? unified-lhs) (succeed? unified-rhs)))
                                            (conj d (disj lhs rhs))
                                            (disj (if (succeed? unified-lhs) lhs (conj d lhs))
                                                  (if (succeed? unified-rhs) rhs (conj d rhs)))) disjs))])
                      (org-display unified unified-lhs unified-rhs)
                      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
                              (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                   (conj-memp simplified-lhs ==?))) ; Only need to check simplified since any non succeed recheck will force a recheck
                          (values unified succeed disunified succeed)
                          (values unified disunified succeed succeed))))))))))

  (org-define (store-constraint s g) ;TODO make store constraint put disj right and everything else left
              ;; Store simplified constraints into the constraint store.
              (cert (state-or-failure? s) (goal? g) (not (conde? g))) ; -> state?
              (exclusive-cond
               [(fail? g) failure]
               [(succeed? g) s]
               [(conj? g) (store-constraint (store-constraint s (conj-car g)) (conj-cdr g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
               [(==? g) (extend s (==-lhs g) (==-rhs g))]
               [else ; All other constraints get assigned to their attributed variables.
                (state-add-constraint s g (list-sort (lambda (v1 v2) (fx< (var-id v1) (var-id v2))) (attributed-vars g)))]))

  (define attributed-vars ;TODO thread trace-goal through other critical infrastructure so its semantically transparent
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (org-case-lambda attr-vars ;TODO create a defrel that encodes context information about what vars were available for use in reasoning about which freshes might be able to unify them within their lexical scope
                     [(g) (let-values ([(vs unifies) (attributed-vars g '() #f)]) vs)]
                     [(g vs unifies)
                      (cert (goal? g))
                      (exclusive-cond
                       [(succeed? g) (values vs unifies)]
                       [(disj? g) (attributed-vars (disj-car g) vs unifies)]
                       #;
                       [(disj? g) (let-values ([(lhs lhs-unifies) (attributed-vars (disj-car g) vs unifies)]) ;TODO do we need to check for recheckable matchos when attributing disj?
                                    (if (conj-memp (disj-car g) ==?) ; Disjunct 2 normalized iff 1 contains no ==
                                        (attributed-vars (disj-car (disj-cdr g)) lhs #t)
                                        (values lhs unifies)))]
                       [(conj? g) (call-with-values
                                      (lambda () (attributed-vars (conj-cdr g) vs unifies))
                                    (lambda (vs unifies) (attributed-vars (conj-car g) vs unifies)))]
                       [(noto? g)
                        (if (==? (noto-goal g))
                            (let ([vs (if (and (var? (==-rhs (noto-goal g))) (not (memq (==-rhs (noto-goal g)) vs))) (cons (==-rhs (noto-goal g)) vs) vs)])
                             (let-values ([(vars _) (attributed-vars (noto-goal g) vs #f)])
                               (values vars unifies)))
                            (let-values ([(vars _) (attributed-vars (noto-goal g) vs #f)])
                              (values vars unifies)))]
                       [(==? g) ;TODO test whether == must attribute to both vars like =/=
                        (cert (var? (==-lhs g)))
                        (values (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs)) #t)
                        #;
                        (let ([vs (if (and (var? (==-rhs g)) (not (memq (==-rhs g) vs))) (cons (==-rhs g) vs) vs)])
                          (values (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs)) #t))]
                       [(matcho? g)
                        (values (if (or (null? (matcho-out-vars g)) (memq (car (matcho-out-vars g)) vs)) vs (cons (car (matcho-out-vars g)) vs)) unifies)]
                       [(pconstraint? g)
                        (values (fold-left (lambda (vs v) (if (memq v vs) vs (cons v vs))) vs (pconstraint-vars g)) unifies)]
                       [(constraint? g) (attributed-vars (constraint-goal g) vs unifies)]
                       [else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])])))
