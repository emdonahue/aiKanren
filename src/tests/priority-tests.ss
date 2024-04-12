(import (test-runner) (mk core) (mk core running) (mk core utils))

(test-suite
 priority
 (parameterize ([search-strategy search-strategy/priority])
   (org-trace
    (tassert "priority no scores"
             (run -1 x1
               (conde
                 [(== x1 1)]
                 [(== x1 2)])) '(1 2)))

   (tassert "priority score reorder"
            (run -1 x1
              (conde
                [(lambda (s p c) (values (== x1 2) (state-priority s 2) p c))]
                [(lambda (s p c) (values (== x1 1) (state-priority s 1) p c))])) '(2 1)))
)
