(library (streams)
  (export step mplus run-stream)
  (import (chezscheme) (state))

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))

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
  
)
