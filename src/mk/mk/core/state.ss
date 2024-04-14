(library (mk core state) ; Main state object that holds substitution & constraints
  (export state-substitution state-varid empty-state set-state-substitution increment-varid set-state-varid
          instantiate-var state-add-constraint unify disunify extend simplify-unification) 
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core streams) (mk core goals) (mk core utils) (mk core mini-substitution) (mk core reducer) (mk core reifier))
  
  ;; === UNIFICATION ===

  
  (define unify ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system. The substitution also contains constraints on the variable, which must be dealt with by the unifier.
    (case-lambda
      [(s d x y) (unify s d x y '())] ; Create an empty list of simplified extension bindings made to the substitution.
      [(s d x y bindings)
       (cert (state? s)) ; -> bindings simplified recheck state
       (let-values ([(x-var x) (walk-var-val s x)]
                    [(y-var y) (walk-var-val s y)])
         (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index. We will be storing y in the x location and the x constraints in the y location, so swapping lets us disambiguate which is which.
             (unify-binding s d y-var y x-var x bindings)
             (unify-binding s d x-var x y-var y bindings)))]))

  (define (unify-binding s d x-var x y-var y bindings) 
    (cert (not (or (goal? x-var) (goal? y-var)))
          (or (not (var? x-var)) (not (var? y-var)) (fx<= (var-id x-var) (var-id y-var)))) ; If both vars, x-var guaranteed to have lower id
    (cond
     
     [(goal? x) 
      (if (goal? y)
          (if (eq? x-var y-var)
              (values bindings succeed succeed succeed d s)
              (extend-constraint s d x-var y-var x y bindings)) ; x->y, y->y, ^cx(y)&cy
          (extend-constraint s d x-var y x succeed bindings))] ; x->y, ^cx(y). y always replaces x if x var, no matter whether y var or const     
     [(eq? x y) (values bindings succeed succeed succeed d s)]
     [(goal? y) (if (var? x)
                    (extend-constraint s d x y-var succeed y bindings) ; x->y, y->y, ^cy. y always replaces x due to id, 
                    (extend-constraint s d y-var x y succeed bindings))] ; y->x, ^cy(x). unless x is a constant.
     [(var? x) (extend-var s d x y bindings)]
     [(var? y) (extend-var s d y x bindings)]
     [(and (pair? x) (pair? y)) 
      (let-values
          ([(bindings simplified committed pending d s) (unify s d (car x) (car y) bindings)])
        (if (fail? bindings)
            (values fail fail fail fail fail failure)
            (let-values ([(bindings simplified^ committed^ pending^ d s) (unify s d (cdr x) (cdr y) bindings)])
              (values bindings (conj simplified simplified^) (conj committed committed^) (conj pending pending^) d s))))]
     [else (values fail fail fail fail fail failure)]))
  
  (define (extend-var s d x y bindings)
    ;; Insert a new binding x->y into the substitution.
    (if (occurs-check/binding s x y) (values fail fail fail fail fail failure)
     (values (cons (cons x y) bindings) succeed succeed succeed (conj d (== x y)) (extend s x y))))

  (define (extend-constraint s d x y x-c y-c bindings)
    ;; Opportunistically simplifies the retrieved constraints using the available vars and vals and then extends the substitution. Since x->y now, we can replace x with y everywhere it appears, and y with y's new value. If there was a constraint on y (and y was a var), we must explicitly remove it since it won't have been overwritten.
    (cert (var? x) (or (not (var? y)) (fx< (var-id x) (var-id y))))
    (if (occurs-check/binding s x y)
        (values fail fail fail fail fail failure)
        ;;let-values ([(x-c/simplified x-c/recheck) (reduce-const2 x-c bindings)])
        (let* ([bindings (cons (cons x y) bindings)]
               [x-c (reduce-constraint2 x-c bindings)]) ;TODO is there ever a reason to simplify y-c? 
          (values bindings succeed x-c y-c (conj d (== x y)) (extend s x y)))
        #;
     (let-values ([(pending committed)
                  
                   (conj-partition (lambda (g) (conj-member g d)) x-c)])
       (let-values ([(committed/simplified committed/recheck) (simplify-unification committed (list (cons x y)))]) ;TODO return y constraint to simplify it with potentially other bindings and also unbind its var?
         (if (or (fail? committed/simplified) (fail? committed/recheck)) (values fail fail fail fail fail failure) ; (if (succeed? val-c) s (remove-constraint s val))
             (let-values ([(pending/simplified pending/recheck) (simplify-unification pending (list (cons x y)))])
               (if (or (fail? pending/simplified) (fail? pending/recheck)) (values fail fail fail fail fail failure) ; (if (succeed? val-c) s (remove-constraint s val))

                   ;; remove var-c constraints from delta
                   ;; add simplified constraints back to delta
                   ;; return separate 
                   (if (occurs-check/binding s x y)
                       (values fail fail fail fail fail failure)
                       (values (cons (cons x y) bindings) (conj committed/simplified pending/simplified) committed/recheck pending/recheck (conj (conj (conj-diff d pending) pending/simplified) (== x y)) (extend s x y))))))))))

  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (cert (state? s) (not (eq? x y)))
    (set-state-substitution
     s (sbral-set-ref
        (state-substitution s)
        (fx- (sbral-length (state-substitution s)) (var-id x)) y succeed)))

  (define (occurs-check/binding s v term) ;TODO see if the normalized ==s can help speed up occurs-check/binding, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification?
    ;; TODO try implementing occurs check in the constraint system and eliminating checks in the wrong id direction (eg only check lower->higher)
    ;; TODO add a non occurs check =!= or ==!
    ;; Returns #t if it detects a cyclic unification.
    ;;TODO remove double occurs check
    (cert (state? s) (var? v))
    (exclusive-cond
     [(eq? v term) #t]            ; term is already walked by normalized ==s
     [(pair? term)
      (or (eq? v (car term)) (eq? v (cdr term)) ; can't just walk a term bc it is already in the substitution
          (occurs-check/binding s v (walk-var s (car term))) (occurs-check/binding s v (walk-var s (cdr term))))]
     [else #f]))

  (define (simplify-unification g s)
    (cert (goal? g))
    (exclusive-cond
     #;
     [(conj? g) (reduce g (== (make-var 0) 1) s)]
     #;
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (simplify-unification (conj-lhs g) s)])
                  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                      (let-values ([(simplified-rhs recheck-rhs) (simplify-unification (conj-rhs g) s)])
     (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
     #;
     [(disj? g) (let*-values ([(simplified-lhs recheck-lhs) (simplify-unification (disj-lhs g) s)]
                              [(lhs) (conj simplified-lhs recheck-lhs)])
                  (if (succeed? lhs) (values succeed succeed)
                      (let*-values ([(simplified-rhs recheck-rhs) (simplify-unification (disj-rhs g) s)]
                                    [(rhs) (conj simplified-rhs recheck-rhs)])
                        
                        (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs)) ;TODO if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked
                                (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                     (conj-memp simplified-lhs (lambda (g) (or (==? g) (and (matcho? g) (null? (matcho-out-vars g))))))))
                            (values succeed (disj-factorized lhs rhs))
                            (values (disj-factorized lhs rhs) succeed)))))]
     
     #;
     [(noto? g) (let-values ([(simplified recheck) (simplify-unification (noto-goal g) s)])
                  (if (succeed? recheck) (values (noto simplified) succeed)
                      (values succeed (noto (conj simplified recheck)))))]
     ;;     [(pconstraint? g) (simplify-unification/pconstraint g s (pconstraint-vars g) #t)]
;;     [(constraint? g) (simplify-unification (constraint-goal g) s)]
;;     [(conde? g) (simplify-unification (conde->disj g) s)]
     #;
     [(matcho? g)
     (let-values ([(normalized out-vars) (mini-reify-normalized s (matcho-out-vars g))]
     [(_ in-vars) (mini-reify-normalized s (matcho-in-vars g))])
     (let ([g (normalize-matcho out-vars in-vars (matcho-goal g))])
     (cond
     [(fail? g) (values fail fail)] ; TODO in simplify matcho, can i just return the g case and let one fail be enough?
     
     [(null? (matcho-out-vars g)) (let-values ([(_ g s^ p) (expand-matcho g empty-state empty-package)])
     (simplify-unification g s))] ; TODO should we thread the real state when expanding matcho while simplifying ==?
     [normalized (values g succeed)]
     [else (values succeed g)])))]
     [else (reduce-constraint g s)]))

  #;
  (define (simplify-unification/pconstraint g s vars normalized) ;TODO refactor pconstraint solving/simplifying to share var iteration code among impls
    (if (null? vars)
        (if normalized (values g succeed) (values succeed g)) 
        (let-values ([(normalized-var walked) (mini-walk-normalized s (car vars))])
          (if (eq? (car vars) walked)
              (simplify-unification/pconstraint g s (cdr vars) (and normalized normalized-var)) ;TODO make == simplifier for pconstraints check for new vars
              (simplify-unification ((pconstraint-procedure g) (car vars) walked g succeed (pconstraint-data g)) s))))
#;
    (values succeed (if (memq v (pconstraint-vars g)) ((pconstraint-procedure g) v x (pconstraint-data g)) g)))

  ;; === DISUNIFICATION ===
  
  (define (disunify s x y)
    ;; Specialized unification for =/= constraints. Only solves enough to confirm non failure and simplifies using special routines for =/=.
    (cert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-var-val s x)]
                 [(y-var y) (walk-var-val s y)]) ;TODO how does disunify play with constraints in substitution?
      (if (eq? x-var y-var) (values fail fail) ; The same variable is never =/= itself regardless of value or constraint.
          (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
              (disunify-binding s y-var y x-var x)
              (disunify-binding s x-var x y-var y)))))

  (define (disunify-binding s x-var x y-var y) ; if x-var and y-var are both vars, x-var has a lower index
              (cert (state? s)) ; -> goal?(disequality) goal?(constraint)
    (cond
     [(goal? x) (extend/disunify s x-var (if (goal? y) y-var y) fail x)] ; Return the constraint on x to recheck for possible == to commit.
     [(goal? y) (if (var? x)
                    (extend/disunify s x y-var fail succeed) ; x is older so it controls the constraints that may pertain to x=/=y. This is a function of the disunifier assigning x=/=y goals to x. If a constraint that might unify could be solved by x=/=y, it would already be attributed to x. Therefore, we only need to add the x=/=y constraint. There is nothing to recheck.
                    (extend/disunify s y-var x fail y))] ; Since x is a value here, treat y like the dominant constraint and simplify it.
     [(eq? x y) (values fail fail)]
     [(var? x) (extend/disunify s x y fail succeed)]
     [(var? y) (extend/disunify s y x fail succeed)]
     [(and (pair? x) (pair? y))
      (let-values ([(lhs c) (disunify s (car x) (car y))])
        (exclusive-cond
         [(succeed? lhs) (values succeed succeed)] ; TODO test whether all the manual checks for fail/succeed could be replaced by conj/disj macros
         [(fail? lhs) (disunify s (cdr x) (cdr y))]
         [else (values (disj lhs (=/= (cdr x) (cdr y))) c)]))]
     [else (values succeed succeed)]))

  (define (extend/disunify s x y d c)
    (if (occurs-check/binding s x y) (values succeed succeed)
     (values (disj (=/= x y) d) c)))
  

  ;; === CONSTRAINTS ===

  
  (define (state-add-constraint s c vs) ;TODO consider sorting ids of variables before adding constraints to optimize adding to sbral. or possibly writing an sbral multi-add that does one pass and adds everything. would work well with sorted lists of attr vars to compare which constraints we can combine while adding
    (cert (state? s) (goal? c) (list? vs))
    ;; Proxy constraints with multiple attributed variables so that they only need to be solved once by whichever variable is checked first and can be removed from the global store so subsequent checks will simply succeed.
    (let ([stored-constraint (substitution-ref (state-substitution s) (car vs))])
      (cert (goal? stored-constraint))
      (fold-left (lambda (s v)
                   (let ([stored-constraint (substitution-ref (state-substitution s) v)])
                     (cert (goal? stored-constraint))
                     (extend s v (conj stored-constraint (proxy (car vs)))))) (extend s (car vs) (conj stored-constraint c)) (cdr vs))))

  (define (remove-constraint s v)
    (extend s v succeed)))
