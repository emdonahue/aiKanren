(library (running)
  (export lazy-run-next lazy-run-step lazy-run-take lazy-run-dfs trace-lazy-run) ;TODO expose more of the lazy-run interface
  (import (chezscheme) (goals) (failure) (state) (datatypes) (utils) (tracing))

  (define (lazy-run-null? r)
    (cert (lazy-run? r))
    (failure? (lazy-run-stream r)))
  
  (define (lazy-run-step r)
    (cert (lazy-run? r))
    (if (state? (lazy-run-stream r)) (make-lazy-run failure (lazy-run-query r) (lazy-run-package r))
     (let-values ([(s p) (stream-step (lazy-run-stream r) (lazy-run-package r))])
       (make-lazy-run s (lazy-run-query r) p))))
  
  (define (lazy-run-pair? r)
    (cert (lazy-run? r))
    (not (failure? (lazy-run-car r))))
  
  (define (lazy-run-car r)
    (cert (lazy-run? r))
    (cond
     [(state? (lazy-run-stream r)) (lazy-run-stream r)]
     [(state+stream? (lazy-run-stream r)) (state+stream-state (lazy-run-stream r))]
     [else failure]))
  
  (define (lazy-run-next r)
    (cert (lazy-run? r))
    (let ([r (lazy-run-step r)])
      (cond
       [(lazy-run-null? r) (values (void) failure r)]
       [(lazy-run-pair? r)
        (if (expand-disjunctions)
            (nyi "expand disj")
            (values ((if (reify-constraints) reify reify-var) (lazy-run-car r) (lazy-run-query r)) (lazy-run-car r) r))]
       [else (lazy-run-next r)])))
  
  (define (lazy-run-take n r)
    (cert (lazy-run? r))
    (if (zero? n) '()
        (let-values ([(reified state r) (lazy-run-next r)])
          (if (failure? state) '() (cons (cons reified state) (lazy-run-take (fx1- n) r))))))

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
