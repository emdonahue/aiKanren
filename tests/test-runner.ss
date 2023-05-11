;;TODO make tassert capture file and line number
(library (test-runner)
  (export tassert)
  (import (chezscheme))
  
  (define (tassert title received expected)
    (when (not (equal? expected received))
      (printf "Failed: ~s~%    Expected: ~s~%    Received: ~s~%"
              title expected received))))
