(import (test-runner) (benchmark-runner))

#;
(define (run-suite filename) ; Automatically load test suites from calling file path.
  (load (string-append (path-parent (car (command-line))) (string (directory-separator)) filename)))

(load "src/tests/sbral-tests.ss")
(load "src/tests/mini-substitution-tests.ss")
(load "src/tests/state-tests.ss")
(load "src/tests/goal-tests.ss")
(load "src/tests/reifier-tests.ss")
(load "src/tests/reducer-tests.ss")
(load "src/tests/solver-tests.ss")
(load "src/tests/matcho-tests.ss")
(load "src/tests/negation-tests.ss")
(load "src/tests/dfs-tests.ss")
(load "src/tests/priority-tests.ss")
(load "src/tests/constraints-tests.ss")
(load "src/tests/lists-tests.ss")
(load "src/tests/tracing-tests.ss")
(load "src/tests/generative-tests.ss")
(load "src/tests/interpreter-tests.ss")

(parameterize ([benchmark-testing #t])
  (load "src/benchmarks/benchmarks.ss"))

(printf "~%Testing Complete: ")
(tmessage)





