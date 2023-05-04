(library (streams)
  (export step mplus run-stream bind* make-unification make-disj run-goal)
  (import (chezscheme) (state))

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  (define-structure (fresh ctn))

  (define (run-goal g s)
    (cond
     [(unification? g)
      (let ([substitution (unify (state-substitution s) (unification-lhs g) (unification-rhs g))])
	(if substitution (make-state substitution) #f))]
     [(disj? g) (mplus (run-goal (disj-lhs g) s) (run-goal (disj-rhs g) s))]
     ))
  
  (define (mplus lhs rhs)
    (cond
     [(not lhs) rhs]
     [(not rhs) lhs]
     [(state? lhs) (cons lhs rhs)]
     [(state? rhs) (cons rhs lhs)]
     [(make-mplus lhs rhs)]))

  (define (step s)
    (cond
     [(not s) #f]
     [(mplus? s) (mplus (step (mplus-rhs s)) (mplus-lhs s))]))

  (define (run-stream s q)
    (cond
     [(not s) '()]
     [(state? s) (list (reify s q))]
     [(pair? s) (cons (reify (car s) q) (run-stream (cdr s) q))]
     [else (run-stream (step s) q)]))

  (define (bind g s)
    (cond
     [(null? s) '()]
     [(state? s) (run-goal g s)]
     [mplus? (make-bind g s)]
     [else (assert #f)]))
  
  (define-syntax bind*
    (syntax-rules ()
      [(_ s) s]
      [(_ s g0 g ...) (bind* (bind g0 s) g ...)]))
  
)
