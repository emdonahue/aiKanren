;;TODO delete streams-tests
(let ([x0 (make-var 0)])
  (tassert "step fail stream" (step #f) #f)
;  (tassert "run state stream" (run-stream (run-goal (== x0 1) empty-state) x0) '(1))
;  (tassert "run disj stream" (run-stream (run-goal (conde (== x0 1) (== x0 2)) empty-state) x0) '(1 2))
  ;(tassert "run unify" (run 1 (q) (== 1 1)) empty-state)
  )