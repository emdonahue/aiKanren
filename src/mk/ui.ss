(library (ui) ;TODO refactor this library into 'vars' and other
  (export run run* run1
          lazy-run
          fresh exist constraint conde
          trace-run)
  (import (chezscheme) (running) (datatypes) (state) (utils) (tracing))

  (define-syntax exist ; Equivalent to fresh, but does not suspend search. Only creates fresh variables.
    (syntax-rules ()
      [(_ q g ...)
       (lambda (start-state p)
         (instantiate-vars [(end-state end-goal) (start-state (conj* g ...) q)] ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
                           (values end-goal end-state p)))]))

  (define-syntax fresh ; Introduce fresh variables.
    ;; (fresh (x y z) ...)
    ;; Can be run with an empty variable list to simply suspend the search at that point.
    (syntax-rules ()
      [(_ q g ...)
       (lambda (start-state p)
         (instantiate-vars [(end-state end-goal) (start-state (conj* g ...) q)] ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
                           (values (suspend end-goal) end-state p)))]))

 (define-syntax conde ; Nondeterministic branching.
   (syntax-rules () 
     [(_ (g ...)) (conj* g ...)] ;TODO make conde do fail checks syntactically
     [(_ c0 c ...)
      (conde-disj (conde c0) (conde c ...))]))

 (define-syntax lazy-run ; Returns a lazy-run object that represents a lazy search stream. The stream can be advanced using the lazy-run-* functions.
   ;; (lazy-run (q ...) g ...)
   (syntax-rules ()
      [(_ q g ...)
       (fresh-vars [start-state (empty-state q)]
           (top-level-runner start-state (vars->list q) (conj* g ...)))]))

 (define-syntax run ; Runs a standard interleaving search and returns the first n answers.
    (syntax-rules ()
      [(_ n q g ...)
       (if (eq? (search-strategy) search-strategy/interleaving)
           (map (if (eq? (answer-type) answer-type/reified) car cdr) (lazy-run-take n (lazy-run q g ...)))
           (run-dfs n (max-depth) q g ...))]))

 (define-syntax run1 ; Returns the first answer instead of a list of answers.
    (syntax-rules ()
      [(_ q g ...)
       (let ([ans (run 1 q g ...)])
         (if (null? ans) (void) (car ans)))]))

   (define-syntax run-dfs ; Depth-first search based run equivalent.
     ;; (run-dfs n depth (q ...) g ...)
     ;; Returns the first n answers, limited to a max search depth of depth.
     (syntax-rules ()
       [(_ n depth () g ...)
        (lazy-run-dfs '() (conj* g ...) empty-state n depth)]
       [(_ n depth (q ...) g ...)
        (fresh-vars [start-state (empty-state (q ...))]
         (lazy-run-dfs (list q ...) (conj* g ...) start-state n depth))]
       [(_ n depth q g ...)
        (fresh-vars [start-state (empty-state (q))]
         (lazy-run-dfs q (conj* g ...) start-state n depth))]))

    (define-syntax run* ; Returns all answers using a depth-first search.
      (syntax-rules ()
        [(_ q g ...)
         (parameterize ([search-strategy search-strategy/dfs]
                        [max-depth -1])
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

   (define-syntax constraint ; Wrapped goals are conjoined and interpreted as a constraint.
     (syntax-rules ()
       [(_ g ...) (let ([c (conj* g ...)]) (if (or (fail? c) (succeed? c)) c (make-constraint c)))])) ;TODO try applying constraint immediately when applied

  ;; === UTILITIES ===

   (define-syntax fresh-vars
     (syntax-rules ()
       [(_ [end-state (start-state '())] body ...)
        (let ([end-state start-state]) body ...)]
       [(_ [end-state (start-state (q ...))] body ...)
        (let* ([vid (state-varid start-state)]
               [q (begin (set! vid (fx1+ vid)) (make-var vid))] ...
               [end-state (set-state-varid start-state vid)])
          body ...)]
       [(_ [end-state (start-state q)] body ...)
        (fresh-vars [end-state (start-state (q))] body ...)]))

   (define-syntax instantiate-vars
     (syntax-rules ()
       [(_ [(end-state end-goal) (start-state start-goal q)] body ...)
        (fresh-vars [intermediate-state (start-state q)]
                    (let* ([end-goal start-goal]
                           [end-state (if (succeed? end-goal) start-state intermediate-state)])
                      body ...))]))

   (define-syntax vars->list
     (syntax-rules ()
       [(_ ()) '()]
       [(_ (q ...)) (list q ...)]
       [(_ q) q]))

    (define (top-level-runner state query conjuncts)
      (make-lazy-run (make-suspended conjuncts state) query empty-package))
)
