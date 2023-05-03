(let ([x0 (make-var 0)])
  (tassert "step fail stream" (step #f) #f)
  (tassert "run state stream" (run-stream (run-goal (== x0 1) empty-state) x0) '(1))
  )
