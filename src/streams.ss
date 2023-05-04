(library (streams)
  (export step mplus run-stream make-unification make-disj run-goal make-runner runner-take)
  (import (chezscheme) (state))

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (suspended goal state))
  
  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))
  
  (define-structure (runner stream query tables))

  (define (set-runner-stream r s)
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) s))

  (define (stream? s)
    (or (mplus? s) (bind? s) (suspended? s) (procedure? s) (null? s) (state? s)))

  (define (run-goal g s r)
    (cond     
     [(disj? g) (mplus (run-goal (disj-lhs g) s r) (run-goal (disj-rhs g) s r))]
     [(procedure? g) (make-suspended g s)]
     [(unification? g) (unify s (unification-lhs g) (unification-rhs g))]
     ))
  
  (define (mplus lhs rhs)
    (cond
     [(not lhs) rhs]
     [(not rhs) lhs]
     [(runner? lhs) (set-runner-stream lhs (mplus (runner-stream lhs) rhs))]
     [(state? lhs) (cons lhs rhs)]
     [(state? rhs) (cons rhs lhs)]
     [(make-mplus lhs rhs)]))

  (define (step s)
    (cond
     [(not s) #f]
     [(mplus? s) (mplus (step (mplus-rhs s)) (mplus-lhs s))]))

  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(null? s) (set-runner-stream r '())]
     [(suspended? s) 3]
     [(mplus? s) (mplus (stream-step (mplus-rhs s) r) (mplus-lhs s))]))

  (define (runner-step r)
    (assert (runner? r))
    (stream-step (runner-stream r) r))

  (define (runner-take n r)
    (runner-step r))

  (define (run-stream s q)
    (cond
     [(not s) '()]
     [(state? s) (list (reify s q))]
     [(pair? s) (cons (reify (car s) q) (run-stream (cdr s) q))]
     [else (run-stream (step s) q)]))

  #;
  (define (bind g s)
    (cond
     [(null? s) '()]
     [(state? s) (run-goal g s)]
     [(mplus? s) (make-bind g s)]
     [else (assert #f)]))

  #;
  (define-syntax bind*
    (syntax-rules ()
      [(_ s) s]
      [(_ s g0 g ...) (bind* (bind g0 s) g ...)]))
  
)
