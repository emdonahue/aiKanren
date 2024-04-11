(library (mk core streams) ; Definitions for core mk goals
  (export empty-state state state? state-substitution state-varid state-attributes set-state-substitution set-state-varid increment-varid set-state-attr state-attr instantiate-var
          empty-substitution
          failure failure?
          package? empty-package
          make-mplus mplus? mplus-lhs mplus-rhs
          make-state+stream state+stream? state+stream-state state+stream-stream
          make-suspended suspended? suspended-goal suspended-state
          maybe-state? stream?)
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core utils))

  
  ;; === FALIURE ===
  (define failure (vector 'failure))
  (define (failure? s) (eq? s failure))

  
  ;; === SUBSTITUTION ===
  (define empty-substitution sbral-empty)


  (define-structure (mplus lhs rhs))

  ;; === SUSPENDED ===
  (define-structure (suspended goal state))

  (define-structure (state+stream state stream)) ; Streams with at least 1 answer state that has completed all current continuation conjuncts.
  

  ;; === STATE ===
  (define-structure (state substitution varid attributes))
  (define state make-state)
  (define empty-state (make-state empty-substitution 0 '()))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
        (make-state substitution (state-varid s) (state-attributes s))
        failure))
  
  (define (increment-varid s)
    (cert (state? s))
    (make-state (state-substitution s) #f (fx1+ (state-varid s))))

  (define (set-state-varid s v)
    (cert (state? s) (number? v) (fx<= (state-varid s) v))
    (if (fx= (state-varid s) v) s
        (make-state (state-substitution s) v (state-attributes s))))

  (define (set-state-attr s pred? data)
    (make-state (state-substitution s) (state-varid s) (cons data (remp pred? (state-attributes s)))))

  (define (state-attr s pred?)
    (find pred? (state-attributes s)))

  (define (instantiate-var s)
    ;; Return a new var and the state with an incremented varid
    (values (make-var (state-varid s)) (increment-varid s)))

  
  ;; === PACKAGE ===
  (define-structure (package data))
  (define empty-package (make-package '()))

  
  ;; === CONTRACTS ===
  (define (maybe-state? s) (or (state? s) (failure? s)))
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (suspended? s) (state? s) (state+stream? s))))
