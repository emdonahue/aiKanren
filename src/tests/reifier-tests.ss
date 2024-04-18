(import (test-runner) (mk core))

(test-suite
 reifier

 (parameterize ([reifier reifier/state])
   (tassert "reifier state" (run1 x1 (== x1 1)) state?))

 (parameterize ([reifier reifier/pretty-print])
   (tassert "reifier state" (run1 (x1 x2) (== x1 x2)) '(_.0 _.0)))

 )
