(library (mk core streams) ; Definitions for core mk goals
  (export empty-state state state? state-substitution state-varid state-attributes set-state-substitution set-state-varid increment-varid state-attr instantiate-var
          empty-substitution
          failure failure?
          package? empty-package
          make-mplus mplus? mplus-lhs mplus-rhs
          make-state+stream state+stream? state+stream-state state+stream-stream
          make-suspended suspended? suspended-goal suspended-state
          state-priority empty-priority-stream make-priority-stream priority-stream-streams priority-stream? priority-< beam-size priority-stream-null? priority-stream-cdr priority-stream-car priority-stream-cons
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

  (define state-attr
    (case-lambda
      [(s pred?) (find pred? (state-attributes s))]
      [(s pred? data) (make-state (state-substitution s) (state-varid s) (cons data (remp pred? (state-attributes s))))]))

  (define (instantiate-var s)
    ;; Return a new var and the state with an incremented varid
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === PRIORITY ===
  (define-structure (search-priority score)) ; A state attribute for storing the priority score of the search branch corresponding to that state.
  
  (define state-priority
    ;; Access or set the priority score of the state depending on num args
    (case-lambda
      [(s) (let ([p (state-attr s search-priority?)])
             (if p (search-priority-score p) 0))]
      [(s p) (state-attr s search-priority? (make-search-priority p))]))


  (define priority-< (make-parameter <)) ; Used to determine priority sort order.
  (define beam-size (make-parameter (most-positive-fixnum))) ; Maximum number of elements allowed in a priority stream
  
  (define-structure (priority-stream streams)) ; A stream type that sorts sub streams by priority score.
  
  (define empty-priority-stream (make-priority-stream '()))
  
  (define (priority-stream-car p)
    (cert (priority-stream? p))
    ;; Retrieve the highest priority stream from the priority-stream
    (car (priority-stream-streams p)))
  
  (define (priority-stream-cdr p)
    (cert (priority-stream? p))
    ;; Retrieve the rest of the priority-stream without its highest priority member
    (make-priority-stream (cdr (priority-stream-streams p))))
  
  (define (priority-stream-null? p)
    (cert (priority-stream? p))
    ;; Test whether the priority stream is empty
    (null? (priority-stream-streams p)))
  
  (define (priority-stream-cons s p)
    (cert (stream? s) (priority-stream? p))
    ;; Add a new substream to the priority-stream in the appropriate priority order
    (make-priority-stream 
     (take (merge (lambda (a b) ((priority-<)
                                 (state-priority (suspended-state b)) ; Suspended streams get sorted by the priority value of their state.
                                 (state-priority (suspended-state a))))
                  (list s) (priority-stream-streams p)) (beam-size))))
  
  
  ;; === PACKAGE ===
  (define-structure (package data))
  (define empty-package (make-package '()))

  
  ;; === CONTRACTS ===
  (define (maybe-state? s) (or (state? s) (failure? s)))
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (suspended? s) (state? s) (state+stream? s) (priority-stream? s))))
