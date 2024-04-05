(begin

  (bench "quine" 100
         ;; Greedily consume ground terms without extending the substitution/store
         (parameterize ([interpreter/number #f]
                        [interpreter/boolean #f]
                        [interpreter/lambda/variadic #f]
                        [interpreter/lambda/multi-arg #f])

           (run 1 (x1) (evalo x1 (list (assq 'list initial-env)) x1)))))
