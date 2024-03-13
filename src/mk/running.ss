(library (running) ; Manages the top level search behaviors and primary user interface.
  (export run run* run1
          lazy-run
          query
          lazy-run-cdr* lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-take)
  (import (chezscheme) (search) (failure) (state) (datatypes) (utils))

  (define query (make-parameter #f)) ; Holds the query variables for inspection by internal elements of the dfs search. Used for debugging.
  
  (define-syntax lazy-run ; Returns a lazy-run stream object that represents a lazy search stream. The stream can be advanced using the lazy-run-* functions.
    ;; (lazy-run (q ...) g ...)
    (syntax-rules ()
      [(_ q g ...)
       (fresh-vars [(start-state start-goal) (empty-state (g ...) q)]
                   (make-lazy-run (make-suspended start-goal start-state) (vars->list q) empty-package))]))

  (define-syntax run ; Runs a standard interleaving search and returns the first n answers.
    (syntax-rules ()
      [(_ n q g ...)
       (if (eq? (search-strategy) search-strategy/interleaving)
           (lazy-run-take n (lazy-run q g ...))
           (fresh-vars [(start-state start-goal) (empty-state (g ...) q)]
                       (parameterize ([query (vars->list q)])
                        (let-values ([(answers p) 
                                      (run-goal-dfs start-goal start-state empty-package n)])
                          (map (lambda (s) (reify-answer (query) s))
                               (reverse answers))))))]))

  (define-syntax run1 ; Returns the first answer instead of a list of answers. Returns (void) if no answers are returned. Useful to quickly obtain an answer without needing to check for failure.
    (syntax-rules ()
      [(_ q g ...)
       (let ([ans (run 1 q g ...)])
         (if (null? ans) (void) (car ans)))]))

  (define-syntax run* ; Returns all answers using a depth-first search. Equivalent to (search-strategy 'dfs), number of answers = -1. Because all answers are returned, the search must be finite, so the more efficient dfs is used in place of interleaving.
    (syntax-rules ()
      [(_ q g ...)
       (parameterize ([search-strategy search-strategy/dfs])
         (run -1 q g ...))]))
  
  (define (lazy-run-null? r)
                                        ; Tests whether the stream is completely exhausted of answers.
    (cert (lazy-run? r))
    (failure? (lazy-run-stream r)))
  
  (define (lazy-run-cdr r)
                                        ; Advances the stream by one step. This may not yield an answer if the resulting stream is still indeterminate. Use lazy-run-car? to test whether the stream has an answer.
    (cert (lazy-run? r))
    (let-values ([(s p) (stream-step (lazy-run-stream r) (lazy-run-package r))])
      (make-lazy-run s (lazy-run-query r) p)))
  
  (define (lazy-run-car? r)
                                        ; Tests whether the stream has a currently available answer that can be retrieved with lazy-run-car.
    (cert (lazy-run? r))
    (or (state? (lazy-run-stream r)) (state+stream? (lazy-run-stream r))))
  
  (define (lazy-run-car r)
                                        ; Returns the currently available answer, or void if none currently exists due to the stream being either indeterminate or exhausted.
    (cert (lazy-run? r))
    (cond
     [(state? (lazy-run-stream r)) (lazy-run-stream r)]
     [(state+stream? (lazy-run-stream r)) (state+stream-state (lazy-run-stream r))]
     [else (void)]))

  (define (lazy-run-cdr* r)
    ;; Applies lazy-run-cdr as often as needed until either lazy-run-null? or lazy-run-car? are true. Does not advance a stream that has a waiting answer or is exhausted.
    (cert (lazy-run? r))
    (if (or (lazy-run-null? r) (lazy-run-car? r)) r (lazy-run-cdr* (lazy-run-cdr r))))
  
  (define (lazy-run-take n r)
    ;; Returns a list of n answers from the lazy-run r.
    (cert (lazy-run? r))
    (if (zero? n) '()
        (let ([r (lazy-run-cdr* r)])
          (if (lazy-run-null? r) '()
              (cons (reify-answer (lazy-run-query r) (lazy-run-car r))
                    (lazy-run-take (fx1- n) (lazy-run-cdr r)))))))

  (define (reify-answer q s) ; Determine the return type based on parameters.
    (cert (state? s))
    (if (eq? (answer-type) answer-type/reified)
        (reify s q) s)))
