(library (running)
  (export run run* run1
          lazy-run
          fresh exist constraint conde
          trace-run
          lazy-run-cdr* lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-take
          lazy-run-dfs
          trace-lazy-run) ;TODO expose more of the lazy-run interface
  (import (chezscheme) (goals) (failure) (state) (datatypes) (utils) (tracing))

  (define-syntax lazy-run ; Returns a lazy-run stream object that represents a lazy search stream. The stream can be advanced using the lazy-run-* functions.
    ;; (lazy-run (q ...) g ...)
    (syntax-rules ()
      [(_ q g ...)
       (fresh-vars [start-state (empty-state q)]
                   (make-lazy-run (make-suspended (conj* g ...) start-state) (vars->list q) empty-package))]))

  (define-syntax run ; Runs a standard interleaving search and returns the first n answers.
    (syntax-rules ()
      [(_ n q g ...)
       (if (eq? (search-strategy) search-strategy/interleaving)
           (lazy-run-take n (lazy-run q g ...))
           (fresh-vars [start-state (empty-state q)]
                       (lazy-run-dfs (vars->list q) (conj* g ...) start-state n (max-depth)))
           )]))

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

  (define-syntax trace-run ; Equivalent to run**-dfs or run*-dfs, but activates tracing system.
    ;; (trace-run (q) g ...)
    ;; (trace-run max-depth (q) g ...)
    ;; The tracing system prints nested debugging information including which trace-goals have been encountered, and various views of the substitution and constraints at each trace-goal. Output is formatted with line-initial asterisks, and is intended to be viewed in a collapsible outline viewer such as Emacs org mode.

    (syntax-rules ()
      [(_ (q ...) g ...) (trace-run -1 (q ...) g ...)]
      [(_ depth () g ...)
       (parameterize ([trace-query '()])
         (trace-lazy-run '() (conj* g ...) empty-state -1))]
      [(_ depth (q) g ...)
       (fresh-vars [start-state (empty-state (q))]

                   (parameterize ([trace-query q])
                     (trace-lazy-run q (conj* g ...) start-state depth)))]
      [(_ depth (q ...) g ...)
       (fresh-vars
        [start-state (empty-state (q ...))]         
        (parameterize ([trace-query (list q ...)])
          (trace-lazy-run (list q ...) (conj* g ...) start-state depth)))]))
  
  (define (lazy-run-null? r)
                                        ; Tests whether the stream is completely exhausted of answers.
    (cert (lazy-run? r))
    (failure? (lazy-run-stream r)))
  
  (define (lazy-run-cdr r)
                                        ; Advances the stream by one step. This may not yield an answer if the resulting stream is still indeterminate. Use lazy-run-car? to test whether the stream has an answer.
    (cert (lazy-run? r))
    (if (state? (lazy-run-stream r)) (make-lazy-run failure (lazy-run-query r) (lazy-run-package r)) 
        (let-values ([(s p) (stream-step (lazy-run-stream r) (lazy-run-package r))])
          (make-lazy-run s (lazy-run-query r) p))))
  
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
                                        ; Applies lazy-run-cdr as often as needed until either lazy-run-null? or lazy-run-car? are true. Does not advance a stream that has a waiting answer or is exhausted.
    (cert (lazy-run? r))
    (if (or (lazy-run-null? r) (lazy-run-car? r)) r (lazy-run-cdr* (lazy-run-cdr r))))
  
  (define (lazy-run-take n r)
                                        ; Returns a list of n answers from the lazy-run r.
    (cert (lazy-run? r))
    (if (zero? n) '()
        (let ([r (lazy-run-cdr* r)])
          (if (lazy-run-null? r) '()
              (cons (if (eq? (answer-type) answer-type/reified)
                        (reify (lazy-run-car r) (lazy-run-query r))
                        (lazy-run-car r))
                    (lazy-run-take (fx1- n) (lazy-run-cdr r)))))))

  (define (lazy-run-dfs q g s n depth)
    (map (lambda (s) (reify s q))
         (let-values ([(ans-remaining answers p) (run-goal-dfs g s empty-package n depth '() succeed)])
           (reverse (if (fx< ans-remaining 0) answers (list-head answers (fx- n (max 0 ans-remaining))))))))

  (define (trace-lazy-run q g s depth)
    (let-values ([(num-remaining answers p)
                  (parameterize ([org-tracing (trace-goals)])
                    (trace-run-goal g s empty-package -1 depth '() open-proof open-proof succeed))])
      (cert (list? answers))
      (map (lambda (ans) (list (reify (trace-answer-state ans) q) (close-proof (trace-answer-proof ans)) (trace-answer-state ans))) (reverse answers)))))
