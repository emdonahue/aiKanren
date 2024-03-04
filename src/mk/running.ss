(library (running)
  (export lazy-run-cdr* lazy-run-null? lazy-run-car? lazy-run-car lazy-run-cdr lazy-run-take lazy-run-dfs trace-lazy-run) ;TODO expose more of the lazy-run interface
  (import (chezscheme) (goals) (failure) (state) (datatypes) (utils) (tracing))

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

  (define (lazy-run-cdr2 r)
    ; Applies lazy-run-cdr as often as needed until either lazy-run-null? or lazy-run-car? are true. Does not advance a stream that has a waiting answer or is exhausted.
    (cert (lazy-run? r))
    (if (or (lazy-run-null? r) (lazy-run-car? r)) r (lazy-run-cdr2 (lazy-run-cdr r))))
  
  (define (lazy-run-cdr* r)
    (cert (lazy-run? r))
    (let ([r (lazy-run-cdr r)])
      (exclusive-cond
       [(lazy-run-null? r) (values (void) failure r)]
       [(lazy-run-car? r)
        (if (expand-disjunctions)
            (nyi "expand disj")
            (values ((if (reify-constraints) reify reify-var) (lazy-run-car r) (lazy-run-query r)) (lazy-run-car r) r))]
       [else (lazy-run-cdr* r)])))
  
  (define (lazy-run-take n r)
    (cert (lazy-run? r))
    (if (zero? n) '()
        (let ([r (lazy-run-cdr2 r)])
          (if (lazy-run-null? r) '()
              (cons (if (eq? (answer-type) answer-type/reified)
                        (reify (lazy-run-car r) (lazy-run-query r))
                        (lazy-run-car r))
                    (lazy-run-take (fx1- n) r))))))

  (define (lazy-run-dfs q g s n depth)
    (map (lambda (s) ((if (reify-constraints) reify reify-var) s q))
         (let-values ([(ans-remaining answers p) (run-goal-dfs g s empty-package n depth '() succeed)])
           (reverse (if (fx< ans-remaining 0) answers (list-head answers (fx- n (max 0 ans-remaining))))))))

  (define (trace-lazy-run q g s depth)
    (let-values ([(num-remaining answers p)
                  (parameterize ([org-tracing (trace-goals)])
                    (trace-run-goal g s empty-package -1 depth '() open-proof open-proof succeed))])
      (cert (list? answers))
      (map (lambda (ans) (list ((if (reify-constraints) reify reify-var) (trace-answer-state ans) q) (close-proof (trace-answer-proof ans)) (trace-answer-state ans))) (reverse answers)))))
