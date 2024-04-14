;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint reduce-const2)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams)) ;TODO remove streams dependency by not expanding matcho without state
  ;;TODO simplify with negated pconstraints as well

  
  (define (reduce-const2 g s)

    (values succeed g))
  
  (define (reduce-constraint g c)
    ;; Reduce existing constraint g using new constraint c, possibly with bindings s.
    (cert (goal? g) (or (goal? c) (mini-substitution? c))) ; -> simplified recheck
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs g) c)])
                  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                      (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs g) c)])
                        (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]
     [(disj? g) (let*-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs g) c)]
                              [(lhs) (conj simplified-lhs recheck-lhs)])
                  (if (succeed? lhs) (values succeed succeed)
                      (let*-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs g) c)]
                                    [(rhs) (conj simplified-rhs recheck-rhs)])
                        
                        (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs)) ;TODO if == simplifier can confirm disj-rhs wont fail, do we need to recheck it? maybe it already contains two disjuncts with == that wont need to be rechecked
                                (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                     (conj-memp simplified-lhs (lambda (g) (or (==? g) (and (matcho? g) (null? (nyi reduce-constraint/matcho) #;(matcho-attributed-vars g)
                                                                                                           )))))))
                            (values succeed (disj-factorized lhs rhs))
                            (values (disj-factorized lhs rhs) succeed)))))]
     #;
     [(conj? g) (let-values ([(simplified-lhs recheck-lhs) (simplify-unification (conj-lhs g) s)])
                  (if (or (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail)
                      (let-values ([(simplified-rhs recheck-rhs) (simplify-unification (conj-rhs g) s)])
     (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs)))))]

     [(noto? g) (let-values ([(simplified recheck) (reduce-constraint (noto-goal g) c)])
                  (if (succeed? recheck) (values (noto simplified) succeed)
                      (values succeed (noto (conj simplified recheck)))))]
     [(constraint? g) (reduce-constraint (constraint-goal g) c)]
     [(conde? g) (reduce-constraint (conde->disj g) c)]
     [else (exclusive-cond
            [(list? c) (reduce-== g c )])])
    )
  
  (define (reduce-== g s)
    (cert (goal? g) (mini-substitution? s))
    (exclusive-cond
     [(or (fail? g) (succeed? g)) (values g g)]
     [(==? g) (let-values ([(s simplified recheck) (mini-simplify s (==-lhs g) (==-rhs g) succeed succeed)])
                (values simplified recheck))]     
     [(matcho? g) (reduce-==/matcho g s)]
     [(pconstraint? g) (reduce-==/pconstraint g s (pconstraint-vars g) #t)]
     [(proxy? g) (if (mini-normalized? s (proxy-var g)) (values succeed succeed) (values succeed g))]
     [else (assertion-violation 'reduce-== "Unrecognized constraint type" g)]))

  (define reduce-==/matcho
    (case-lambda
      [(g s)
       (let ([s^ (mini-unify-substitution s (matcho-substitution g))])
         (if (failure? s^) (values fail fail) (reduce-==/matcho g s (matcho-substitution) '() #t)))]
      [(g s sub sub^ normalized?)
       (if (null? sub)
           (let ([g (make-matcho sub^ (matcho-ctn g))])
             (if normalized? (values g succeed) (values succeed g)))
           (let* ([lhs (caar sub)]
                  [rhs (cdar sub)])
             (nyi reducer matcho)
             #;
             (let-values ([(rhs-normalized? rhs) (mini-reify-normalized s^ rhs)])
               (reduce-==/matcho g s (cdr sub) (cons (cons lhs rhs) sub^)
                                 (and normalized? rhs-normalized
                                      (or (zero? (var-id lhs))
                                          (mini-normalized s lhs)))))))]))
  
  (define (reduce-==/pconstraint g s vars normalized?)
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (if (null? vars)
        (if normalized? (values g succeed) (values succeed g)) 
        (let-values ([(var-normalized? walked) (mini-walk-normalized s (car vars))])
          (if (eq? (car vars) walked) ; If any have been updated, run the pconstraint.
              (reduce-==/pconstraint g s (cdr vars) (and normalized? var-normalized?))
              (reduce-constraint ((pconstraint-procedure g) (car vars) walked g succeed g) s)))))

  )
