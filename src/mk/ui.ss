(library (ui) ;TODO refactor this library into 'vars' and other
  (export run run* run1
          runner
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

 (define-syntax runner ; Returns a runner object that represents a lazy search. The stream can be advanced using runner-next to receive three values: the next complete answer, the state representing that answer, and another runner waiting to seek the next answer.
   ;; (runner (q ...) g ...)
   (syntax-rules ()
      [(_ q g ...)
       (fresh-vars empty-state start-state q
           (top-level-runner start-state (vars->list q) (conj* g ...)))]))

 (define-syntax run ; Runs a standard interleaving search and returns the first n answers.
    (syntax-rules ()
      [(_ n q g ...)
       (if (eq? (search-strategy) search-strategy/interleaving)
           (map (if (eq? (answer-type) answer-type/reified) car cdr) (runner-take n (runner q g ...)))
           (run-dfs n (max-depth) q g ...))]))

 (define-syntax run1 ; Returns the first answer instead of a list of answers.
    (syntax-rules ()
      [(_ q g ...)
       (let ([ans (run 1 q g ...)])
         (if (null? ans) (void) (car ans)))]))

 #;
   (define-syntax run-states ; Equivalent to run, but returns state objects for further processing.
    (syntax-rules ()
      [(_ n (q ...) g ...)
       (map cdr (runner-take n (runner (q ...) g ...)))]))

 #;
   (define-syntax run1-state ; Equivalent to run1, but returns state objects for further processing.
    (syntax-rules ()
      ((_ (q ...) g ...)
       (let ([ans (run-states 1 (q ...) g ...)])
         (if (null? ans) failure (car ans))))))


   (define-syntax run-dfs ; Depth-first search based run equivalent.
     ;; (run-dfs n depth (q ...) g ...)
     ;; Returns the first n answers, limited to a max search depth of depth.
     (syntax-rules ()
       [(_ n depth () g ...)
        (runner-dfs '() (conj* g ...) empty-state n depth)]
       [(_ n depth (q ...) g ...)
        (fresh-vars empty-state start-state (q ...)
         (runner-dfs (list q ...) (conj* g ...) start-state n depth))]
       [(_ n depth q g ...)
        (fresh-vars empty-state start-state (q)
         (runner-dfs q (conj* g ...) start-state n depth))]))

    (define-syntax run* ; Returns all answers using a depth-first search.
      (syntax-rules ()
        [(_ q g ...)
         (parameterize ([search-strategy search-strategy/dfs]
                        [max-depth -1])
          (run -1 q g ...))]))

    #;
   (define-syntax run1-dfs ; Returns one answer from a dfs search at any depth. Equivalent to (run-dfs 1 -1 ...).
     ;; (run1-dfs depth (q ...) g ...)
     (syntax-rules ()
       [(_ q g ...)
        (let ([answers (run-dfs 1 -1 q g ...)])
          (if (null? answers) (void) (car answers)))]))

   (define-syntax trace-run ; Equivalent to run**-dfs or run*-dfs, but activates tracing system.
     ;; (trace-run (q) g ...)
     ;; (trace-run max-depth (q) g ...)
     ;; The tracing system prints nested debugging information including which trace-goals have been encountered, and various views of the substitution and constraints at each trace-goal. Output is formatted with line-initial asterisks, and is intended to be viewed in a collapsible outline viewer such as Emacs org mode.

     (syntax-rules ()
       [(_ (q ...) g ...) (trace-run -1 (q ...) g ...)]
       [(_ depth () g ...)
        (parameterize ([trace-query '()])
          (trace-runner '() (conj* g ...) empty-state -1))]
       [(_ depth (q) g ...)
        (fresh-vars empty-state start-state (q)

         (parameterize ([trace-query q])
             (trace-runner q (conj* g ...) start-state depth)))]
       [(_ depth (q ...) g ...)
        (fresh-vars
         empty-state start-state (q ...)
         (parameterize ([trace-query (list q ...)])
             (trace-runner (list q ...) (conj* g ...) start-state depth)))]))

   (define-syntax constraint ; Wrapped goals are conjoined and interpreted as a constraint.
     (syntax-rules ()
       [(_ g ...) (let ([c (conj* g ...)]) (if (or (fail? c) (succeed? c)) c (make-constraint c)))])) ;TODO try applying constraint immediately when applied

  ;; === UTILITIES ===

   (define-syntax fresh-vars
     (syntax-rules ()
       [(_ start-state end-state '() body ...)
        (let ([end-state start-state]) body ...)]
       [(_ start-state end-state (q ...) body ...)
        (let* ([vid (state-varid start-state)]
               [q (begin (set! vid (fx1+ vid)) (make-var vid))] ...
               [end-state (set-state-varid start-state vid)])
          body ...)]
       [(_ start-state end-state q body ...)
        (fresh-vars start-state end-state (q) body ...)]))

   (define-syntax instantiate-vars
     (syntax-rules ()
       [(_ [(end-state end-goal) (start-state start-goal q)] body ...)
        (fresh-vars start-state intermediate-state q
                    (let* ([end-goal start-goal]
                           [end-state (if (succeed? end-goal) start-state intermediate-state)])
                      body ...))]))

   (define-syntax vars->list
     (syntax-rules ()
       [(_ ()) '()]
       [(_ (q ...)) (list q ...)]
       [(_ q) q]))

    (define (top-level-runner state query conjuncts)
      (make-runner (make-suspended conjuncts state) query empty-package)))
