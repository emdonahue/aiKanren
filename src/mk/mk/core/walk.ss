(library (mk core walk) ; Responsible for walking vars
  (export  walk walk-var walk-var-val substitution-ref walk-var*)
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core streams) (mk core utils) (mk core goals) (mk core mini-substitution))

  (define (walk s v)
    (cert (state? s)) ; -> (or ground? var? constraint?)
    (let-values ([(binding v) (walk-var-val s v)]) v))

  (define (walk-var s v)
    (cert (state? s)) ; (or ground? var?)
    (let-values ([(lvar val) (walk-var-val s v)])
      (if (goal? val) ; If val is a constraint, the var is still free, so return it.
          lvar val)))

  (define (walk-var-val s v)
    ;; Returns the value or constraints on v, and whatever is the last logic variable in the chain.
    (cert (state? s)) ; -> (or var? ground?) (or (ground? var? constraint?)
    (walk-binding (state-substitution s) v))

  (define (walk-var* s v)
    (cert (or (state? s) (mini-substitution? s))
          (if (state? s) (walk-var s v) (mini-walk s v))))
  
  (define (walk-binding s v)
    ;; Returns the walked value or constraint of v and whatever is the last logic variable in the chain (possibly equal to the value if the var is completely free). If v is ground, it will return two grounds.
    (cert (sbral? s) (not (and (var? v) (zero? (var-id v))))) ; -> (or var? ground?) (or ground? var? constraint?)
    (if (var? v)
        (let ([walked (substitution-ref s v)])
          (exclusive-cond
           [(succeed? walked) (values v v)]
           [(var? walked) (walk-binding s walked)]
           [else (values v walked)]))
        (values v v)))

  (define (substitution-ref s v)
    ;; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
    (cert (sbral? s) (var? v))
    (sbral-ref s (fx- (sbral-length s) (var-id v)) succeed)))
