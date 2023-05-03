(library (streams)
  (export step mplus)
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
  
)
