(library (all-tests)
  (export run-all-tests)
  (import (chezscheme) (aikanren) (test-runner) (benchmark-runner) (sbral-tests) (state-tests) (solver-tests) (constraints-tests) (negation-tests) (mini-substitution-tests) (listo-tests) (matcho-tests) (goals-tests) (quine-tests) (interpreter-tests) (dfs-tests) (tracing-tests))

  (define (run-all-tests)
    (run-sbral-tests)
    (run-mini-substitution-tests)
    (run-state-tests)
    (run-goal-tests)
    (run-solver-tests)
    (run-matcho-tests)
    (run-negation-tests)
    (run-dfs-tests)
    (run-constraints-tests)
    (run-listo-tests)
    (run-tracing-tests)
#;
    (begin 
      (run-quine-tests)
      (run-interpreter-tests)

      (parameterize ([benchmark-testing #t])
	(include "src/benchmarks/benchmarks.ss")))))
