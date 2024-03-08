;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (reducer)
  (export reduce-constraint)
  (import (chezscheme) (datatypes) (mini-substitution) (utils) (negation))
  ;;TODO simplify with negated pconstraints as well

  (define (reduce-constraint g c s)
    (cert (goal? g) (goal? c) (mini-substitution? s)) ; -> simplified recheck
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs g) c s)])
                  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                      (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs g) c s)])
                        (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
     [(disj? g) (let*-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs g) c s)]
                              [(lhs) (conj simplified-lhs recheck-lhs)])
                  (if (succeed? lhs) (values succeed succeed)
                      (let*-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs g) c s)]
                                    [(rhs) (conj simplified-rhs recheck-rhs)])
                        
                        (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs)) ;TODO if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked
                                (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                     (conj-memp simplified-lhs (lambda (g) (or (==? g) (and (matcho? g) (null? (matcho-out-vars g))))))))
                            (values succeed (disj-factorized lhs rhs))
                            (values (disj-factorized lhs rhs) succeed)))))]
     #;
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (simplify-unification (conj-lhs g) s)])
                  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                      (let-values ([(simplified-rhs recheck-rhs) (simplify-unification (conj-rhs g) s)])
     (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]

     [(noto? g) (let-values ([(simplified recheck) (reduce-constraint (noto-goal g) c s)])
                  (if (succeed? recheck) (values (noto simplified) succeed)
                      (values succeed (noto (conj simplified recheck)))))]
     [(constraint? g) (reduce-constraint (constraint-goal g) c s)]
     [(procedure? g) (reduce-constraint (g empty-state empty-package) c s)]
     [(conde? g) (reduce-constraint (conde->disj g) c s)]
     [else (exclusive-cond
            [(==? c) (reduce-== g c s)])])
    )

  (define (reduce-== g c s)
    (cert (goal? g) (goal? c) (mini-substitution? s))
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]
     [(==? g) (let-values ([(s simplified recheck) (mini-simplify s (==-lhs g) (==-rhs g) succeed succeed)])
                (values simplified recheck))]     
     [(matcho? g) (reduce-==/matcho g c s)]
     [(pconstraint? g) (reduce-==/pconstraint g c s (pconstraint-vars g) #t)]
     [(proxy? g) (if (mini-normalized? s (proxy-var g)) (values succeed succeed) (values succeed g))]
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define (reduce-==/matcho g c s)
    (let-values ([(normalized out-vars) (mini-reify-normalized s (matcho-out-vars g))]
                 [(_ in-vars) (mini-reify-normalized s (matcho-in-vars g))])
      (let ([g (normalize-matcho out-vars in-vars (matcho-goal g))])
        (cond
         [(fail? g) (values fail fail)] ; TODO in simplify matcho, can i just return the g case and let one fail be enough?
         [(not (matcho? g)) (reduce-constraint g c s)]
         [(null? (matcho-out-vars g)) (let-values ([(_ g s^ p) (expand-matcho g empty-state empty-package)])
                                        (reduce-constraint g c s))] ; TODO should we thread the real state when expanding matcho while reducing ==?
         [normalized (values g succeed)]
         [else (values succeed g)]))))
  
  (define (reduce-==/pconstraint g c s vars normalized)
    (if (null? vars)
        (if normalized (values g succeed) (values succeed g)) 
        (let-values ([(normalized-var walked) (mini-walk-normalized s (car vars))])
          (if (eq? (car vars) walked)
              (reduce-==/pconstraint g c s (cdr vars) (and normalized normalized-var))
              (reduce-constraint ((pconstraint-procedure g) (car vars) walked g succeed g) c s)))))

  )
