;TODO delete datatypes.ss and break it into smaller libs
(library (datatypes)
  (export expand-disjunctions  

          package? empty-package
          fresh-vars vars->list
          stream?
          failure failure?
          var make-var var? var-id set-var-id!
          make-suspended  suspended? suspended-goal suspended-state
          make-mplus mplus? mplus-lhs mplus-rhs
          make-state+stream state+stream? state+stream-state state+stream-stream
          maybe-state?
          empty-state state? state-substitution state-varid set-state-substitution set-state-varid increment-varid instantiate-var set-state-datum state-datum
          empty-substitution
          constraint? constraint-goal  proxy proxy? proxy-var constraint
          goal?
          succeed fail succeed? fail?
          fresh exist conde
          make-== == ==? ==-lhs ==-rhs
          suspend suspend? suspend-goal
          dfs-goal dfs-goal? dfs-goal-procedure
          make-conj conj conj?  conj-lhs conj-rhs conj* conj-memp conj-fold conj-filter conj-diff conj-member conj-memq conj-intersect conj-partition ;TODO replace conj-car/cdr with lhs/rhs
          make-disj disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs disj-succeeds? disj-factorize disj-factorized
          conde-disj conde? conde-lhs conde-rhs conde-car conde-cdr conde->disj
          pconstraint? pconstraint pconstraint-vars pconstraint-data pconstraint-procedure pconstraint-rebind-var pconstraint-check pconstraint-attributed?
          make-matcho matcho? matcho-out-vars matcho-in-vars matcho-goal  normalize-matcho matcho-attributed? matcho-test-eq?
          ;expand-matcho
          make-noto noto? noto-goal
          __)
  (import (chezscheme) (sbral) (variables) (goals) (streams) (utils))

  
  
  
  (define expand-disjunctions (make-parameter #f)) ;TODO implement expand disjunction constraints in reifier. eg turn a bool constraint into a stream of t f.
  
  

  
  

  

  
  ;; === GOALS ===
  
  
  
  (define (normalize-matcho out in proc) ;TODO see if normalize-matcho adds anything to solve-matcho
    (cert (not (and (null? out) (null? in))))
    (exclusive-cond
     [(null? out)
      (let-values ([(_ g s p) (proc empty-state empty-package in)]) g)]
     [(var? (car out)) (make-matcho out in proc)]
     [else (if (pair? (car out)) (normalize-matcho (cdr out) (cons (car out) in) proc) fail)]))

  (define (expand-matcho g s p)
    ;; Runs the matcho goal with whatever ground variables have already been provided, assuming the remaining variables are unbound.
    ((matcho-goal g) s p (matcho-in-vars g)))

  (define (matcho-attributed? g var)
    (memq var (matcho-out-vars g)))

  (define (matcho-test-eq? g out in) ; Shorthand for checking the comparable properties of matcho during unit testing.
    (and (matcho? g) (equal? (matcho-out-vars g) out) (equal? (matcho-in-vars g) in)))


  

  )
