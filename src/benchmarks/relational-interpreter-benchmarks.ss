(begin
  (parameterize ([interpreter/number #f]
                 [interpreter/boolean #f]
                 [interpreter/lambda/variadic #f]
                 [interpreter/lambda/multi-arg #f]
                 [interpreter/if #f]
                 [interpreter/letrec #f])
    (let ([env (list (assq 'list initial-env))])
     (bench "relinterp - quine" 100
            (run 1 (x1) (evalo x1 env x1)))

     (bench "relinterp - twine" 20
            (run1 (x1 x2) (=/= x1 x2)
                  (evalo x1 env x2)
                  (evalo x2 env x1)))))

  (parameterize ([interpreter/number #f]
                 [interpreter/boolean #f]
                 [interpreter/lambda #f]
                 [interpreter/letrec #f]
                 [interpreter/quote #f]
                 [max-depth 70])
    (let ([env (filter (lambda (b) (memq (car b) '(null? cons car cdr))) initial-env)])
      (bench "relinterp - append" 1
             (run1 (body)
                (synthesizeo `(if (null? a) b (cons (car a) (f ,body b)))
                             '(
                               ((() (1)) . (1))
                               (((1) (2)) . (1 2))
                               )
                             env))))))
