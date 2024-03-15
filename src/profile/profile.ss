(import (benchmark-runner))

(parameterize ([benchmark-testing #t])
 (load "src/benchmarks/benchmarks.ss"))
