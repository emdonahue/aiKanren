(library (benchmark-runner)
  (import (rnrs))
  (export bench)

 (define (bench p)
   (time p)))
