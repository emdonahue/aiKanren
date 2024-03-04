(library (ui) ;TODO refactor this library into 'vars' and other
  (export run run* run1
          lazy-run
          fresh exist constraint conde
          trace-run)
  (import (chezscheme) (running) (datatypes) (state) (utils) (tracing) (datatypes))

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

    

  ;; === UTILITIES ===
)
