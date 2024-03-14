(library (streams) ; Definitions for core mk goals
  (export empty-state state? state-substitution state-varid set-state-substitution set-state-varid increment-varid set-state-datum state-datum instantiate-var
          empty-substitution
          failure failure?
          maybe-state?)
  (import (chezscheme) (sbral) (variables) (utils))

  ;; === FALIURE ===
  (define failure (vector 'failure))
  (define (failure? s) (eq? s failure))

  ;; === SUBSTITUTION ===
  (define empty-substitution sbral-empty)
  

  ;; === STATE ===
  (define-structure (state substitution varid data))
  
  (define empty-state (make-state empty-substitution 0 '()))

  (define (set-state-substitution s substitution) ;TODO try replacing state vector copy with manual updates using mutators
    (if (not (failure? substitution))
        (let ([s (vector-copy s)])
          (set-state-substitution! s substitution) s) substitution))
  
  (define (increment-varid s)
    (cert (state? s))
    (make-state (state-substitution s) #f (fx1+ (state-varid s))))

  (define (set-state-varid s v)
    ;;TODO remove set-state-varid
    (cert (state? s) (number? v) (fx<= (state-varid s) v))
    (if (fx= (state-varid s) v) s
        (let ([s (vector-copy s)])
          (set-state-varid! s v) s)))

  (define (set-state-datum s pred? data)
    (make-state (state-substitution s) (state-varid s) (cons data (remp pred? (state-data s)))))

  (define (state-datum s pred?)
    (find pred? (state-data s)))

  (define (instantiate-var s)
    ;; Return a new var and the state with an incremented varid
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === CONTRACTS ===
  (define (maybe-state? s) (or (state? s) (failure? s))) ;TODO rename maybe-state? to maybe-state?
  )
