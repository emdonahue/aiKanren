(library (tracing)
  (export trace-run 
          trace-query trace-run-goal trace-goal trace-conde trace-proof-goals trace-goals
          open-proof close-proof
          trace-answer-proof trace-answer-state)
  (import (chezscheme) (datatypes) (solver) (utils) (state) (debugging))

  (define trace-query (make-parameter #f)) ; Query variables used to generate trace debug information. Set internally by trace-run. #f is used to signify that the tracing subsystem is not running.
  (define trace-proof-goals (make-parameter #t)) ; A flag to enable or disable use of the proof subsystem during tracing.
  (define trace-goals (make-parameter #t)) ; A flag to enable or disable trace printing.
  (define-structure (trace-answer theorem proof state))

  (define-structure (trace-data theorem proof))
  (define (state-theorem s)
    (cert (state? s))
    (trace-data-theorem (state-datum s trace-data?)))
  (define (state-proof s)
    (cert (state? s))
    (trace-data-proof (state-datum s trace-data?)))
  (define (set-state-trace s theorem proof)
    (cert (state? s))
    (set-state-datum s trace-data? (make-trace-data theorem proof)))
  
  ;; === INTERFACE ===
  
  (define-syntax trace-goal ; Wraps one or more goals and adds a level of nesting to the trace output.
    ;; (trace-goal name goals...)
    ;; When the trace is printing, goals wrapped in trace-goal will print within a nested hierarchy under a new heading titled <name>.
    (syntax-rules ()
                                        ;TODO make goal-cond automatically add a condition for trace goals when not compiling and make trace goals vanish when compiling (test (optimize-level) param?
      [(_ name goals ...)
       (if (trace-query)
           (make-trace-goal 'name '(goals ...) (conj* goals ...))
           (conj* goals ...))]))
  
  (define-syntax trace-conde ; Equivalent to conde but each branch begins with a name and implicitly instantiates a trace-goal.
    ;; (trace-conde [name1 g1 ...] [name2 g2 ...] ...)
    (syntax-rules ()
      [(_ (name g ...))
       (trace-goal name g ...)]
      [(_ c0 c ...) (conde-disj (trace-conde c0) (trace-conde c ...))]))

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
       (parameterize ([trace-query #t])
         (fresh-vars [(start-state start-goal) (empty-state (g ...) (q))]
                     (parameterize ([trace-query q])
                       (trace-lazy-run q start-goal start-state depth))))]
      [(_ depth (q ...) g ...)
       (parameterize ([trace-query #t])
         (fresh-vars
          [(start-state start-goal) (empty-state (g ...) (q ...))]         
          (parameterize ([trace-query (list q ...)])
            (trace-lazy-run (list q ...) start-goal start-state depth))))]))
  
  (define (trace-lazy-run q g s depth)
    (let-values ([(num-remaining answers p)
                  (parameterize ([org-tracing (trace-goals)])
                    (trace-run-goal g (set-state-datum s trace-data? (make-trace-data open-proof open-proof)) empty-package -1 depth '() succeed))])
      (cert (list? answers))
      (map (lambda (ans) (list (reify (trace-answer-state ans) q) (close-proof (trace-answer-proof ans)) (trace-answer-state ans))) (reverse answers))))
  
  ;; === INTERPRETER ===

  (define (trace-run-goal g s p n depth answers ctn) ;TODO might be able to fold proofs into standard dfs with parameters and get rid of special cps trace interpreter
                                        ;(display (state-datum s trace-data?))
    #;
    (when (not (failure? s))
      (printf "aproof: ~s sproof: ~s~%" proof (trace-data-proof (state-datum s trace-data?))))
    #;
    (cert (or (failure? s) (equal? proof (trace-data-proof (state-datum s trace-data?)))
              (equal? theorem (trace-data-theorem (state-datum s trace-data?)))))
    (cond
     [(failure? s) (values n answers p)]
     [(succeed? g) (if (succeed? ctn)
                       (values (fx1- n) (cons (make-trace-answer (state-theorem s) (state-proof s) s) answers) p)
                       (trace-run-goal ctn s p n depth answers succeed))]
     [(zero? depth) (print-depth-limit (state-theorem s)) (values n answers p)]
     [(conj? g) (trace-run-goal (conj-lhs g) s p n depth answers (conj (conj-rhs g) ctn))]
     [(conde? g) (let-values ([(num-remaining answers p) (trace-run-goal (conde-lhs g) s p n depth answers ctn)])
                   (if (zero? num-remaining) (values num-remaining answers p)
                       (trace-run-goal (conde-rhs g) s p num-remaining depth answers ctn)))]
     [(matcho? g) (let-values ([(_ g s p) (expand-matcho g s p)])
                    (trace-run-goal g s p n (fx1- depth) answers ctn))]     
     [(procedure? g) (let-values ([(g s p ctn) (g s p ctn)])
                       (trace-run-goal g s p n (fx1- depth) answers ctn))]
     [(trace-goal? g) (cps-trace-goal g s p n depth answers (state-proof s) (state-theorem s) ctn)]
     [(proof-goal? g) (trace-run-goal (proof-goal-goal g) (set-state-datum s trace-data? (make-trace-data (proof-goal-proof g) (state-proof s))) p n depth answers ctn)]
     [else (trace-run-goal ctn (run-constraint g s) p n depth answers succeed)]))

  (define (cps-trace-goal g s p n depth answers proof theorem ctn)
    (if (theorem-contradiction theorem (trace-goal-name g)) ; If the current theorem path diverges from the required proof,
        (trace-run-goal fail s p n depth answers ctn) ; fail immediately.
        (let ([subgoal (trace-goal-goal g)]
              [proof (open-subproof proof (trace-goal-name g))]
              [subtheorem (subtheorem theorem)]
              [ctn (lambda (s p c)
                     (if (theorem-contradiction (state-theorem s) '()) 
                         (values fail failure p fail)
                         (values ctn (set-state-trace s (subtheorem (state-theorem s)) (close-subproof (state-proof s))) p c)))])
          (if (tracing? theorem)
              (begin
                (org-print-header (trace-goal-name g))           
                (parameterize ([org-depth (fx1+ (org-depth))])
                  (when (tracing? theorem) (print-trace-args g s proof))
                  (let*-values ([(ans-remaining answers p)
                                 (trace-run-goal subgoal
                                                 (set-state-datum s trace-data? (make-trace-data subtheorem proof))
                                                 p n depth answers ctn)]) ;proof subtheorem
                    (when (theorem-trivial? theorem)
                      (if (null? answers) (org-print-header "<failure>")
                          (begin (org-print-header "<answers>")
                                 (for-each (lambda (i a)
                                             (parameterize ([org-depth (fx1+ (org-depth))])
                                               (org-print-header (number->string i))
                                               (parameterize ([org-depth (fx1+ (org-depth))])
                                                 (print-trace-answer (trace-answer-proof a) (trace-answer-state a))))) (enumerate answers) answers))))
                    (values ans-remaining answers p))))
              (trace-run-goal subgoal (set-state-trace s subtheorem proof) p n depth answers ctn)))))
  
  ;; === PRINTING ===
  
  (define (print-trace-args g s proof)
    (org-print-header "<arguments>")
    (parameterize ([org-depth (fx1+ (org-depth))])
      (print-trace-answer proof s)
      (print-trace-goal g)))

  (define (print-trace-goal g)
    (org-print-header "source")
    (for-each org-print-item (trace-goal-source g))
    (org-print-header "simplified")
    (org-print-item (trace-goal-goal g)))
  
  (define (print-trace-answer proof s)
    (org-print-header "proof")
    (org-print-item (reverse-proof proof))
    (org-print-header "query")
    (org-print-item (reify-var s (trace-query)))
    (let* ([substitution (walk-substitution s)] ;TODO print unbound variables in substitution debugging by checking var id in state
           [constraints (filter (lambda (b) (and (goal? (cdr b)) (not (succeed? (cdr b))))) substitution)])
      (unless (null? constraints)
        (org-print-header "constraints")
        (for-each (lambda (b) (org-print-item (car b) (cdr b))) constraints))
      (unless (null? substitution)
        (org-print-header "substitution")
        (for-each (lambda (b) (org-print-item (car b) (cdr b))) substitution))))

  (define (print-depth-limit theorem)
    (when (tracing? theorem) (org-print-header " <depth limit reached>")))

  ;; === PROOFS ===
  
  (define cursor '__)
  (define (cursor? c) (eq? c cursor))

  (define open-proof (list cursor))
  
  (define (close-proof proof)
    (reverse-proof (cdr proof)))
  
  (define (open-subproof proof name)
    (if (cursor? (car proof)) (cons (list cursor name) (cdr proof))
        (cons (open-subproof (car proof) name) (cdr proof))))

  (define (close-subproof proof)
    (if (cursor? (caar proof)) (cons* cursor (cdar proof) (cdr proof))
        (cons (close-subproof (car proof)) (cdr proof))))
  
  (define (reverse-proof proof)
    (if (pair? proof) (reverse (map reverse-proof proof)) proof))

  (define (theorem-contradiction theorem term)
    (if (pair? theorem) (theorem-contradiction (car theorem) term) (not (or (eq? theorem cursor) (eq? theorem term)))))

  (define (subtheorem theorem)
    (if (pair? theorem)
        (if (pair? (car theorem)) (cons (subtheorem (car theorem)) (cdr theorem))
            (if (cursor? (car theorem)) cursor (cdr theorem))) theorem))

  (define (tracing? theorem)
    (or (trace-proof-goals) (theorem-trivial? theorem)))

  (define (theorem-trivial? theorem)
    (if (pair? theorem) (theorem-trivial? (car theorem)) (cursor? theorem))))
