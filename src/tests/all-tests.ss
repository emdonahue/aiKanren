(import (test-runner))

(load "goal-tests.ss")
(load "constraints-tests.ss")

(printf "~%Testing Complete: ")
(tmessage)


#;
((run-sbral-tests)
 (run-mini-substitution-tests)
 (run-state-tests)
 (run-goal-tests)
 (run-reducer-tests)
 (run-solver-tests)
 (run-matcho-tests)
 (run-negation-tests)
 (run-dfs-tests)
 (run-constraints-tests)
 (run-listo-tests)
 (run-tracing-tests)
 (run-generative-tests)
 (run-quine-tests)
 (run-interpreter-tests)
 (parameterize ([benchmark-testing #t])
   (include "src/benchmarks/benchmarks.ss")))
