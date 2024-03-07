(library (tracing-tests)
  (export run-tracing-tests)
  (import (chezscheme) (test-runner) (aikanren) (utils) (debugging) (datatypes) (tracing))

  (define x1 (make-var 1))
  (define x2 (make-var 2))
  
  (define (run-tracing-tests)
    
    (parameterize ([trace-goals #f])
      (tassert "trace ==" (trace-run* x1 (== x1 1)) '(1))
      (tassert "trace ==" (trace-run* x1 (== x1 1)) '(1))
      (tassert "trace == & ==" (trace-run* (x1 x2) (conj* (== x1 1) (== x2 2))) '((1 2)))
      (tassert "trace == & == depth 1" (trace-run* (x1 x2) (== x1 1) (== x2 2)) '((1 2)))
      (tassert "trace == | ==" (trace-run* x1 (conde [(== x1 1)] [(== x1 2)])) '(1 2))
      (tassert "trace exist" (trace-run* x1 (exist (x2) (== x1 x2) (== x2 1))) '(1))
      (tassert "trace fresh" (trace-run* x1 (fresh (x2) (== x1 x2) (== x2 1))) '(1))
      (tassert "trace matcho" (trace-run* x1 (matcho ([x1 (a . d)]) (== a 1) (== d 2))) '((1 . 2)))
      (tassert "trace fail if constraint fails" (trace-run* x1 (conde [(== x1 3) (conde [(== x1 1)] [(== x1 2)])] [(== x1 2)])) '(2))

      (parameterize ([answer-type answer-type/state])
        (tassert "proof constraint"
                 (state-proof (car (trace-run* x1 (trace-goal x1=1 (== x1 1))))) '((x1=1)))
        (tassert "proof trace-conde"
                 (map state-proof (trace-run* x1 (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)]))) '(((x1=1)) ((x1=2))))
        (tassert "proof conj"
                 (map state-proof (trace-run* (x1 x2) (trace-goal x1=1 (== x1 1)) (trace-goal x2=2 (== x2 2)))) '(((x1=1) (x2=2))))
        (tassert "proof conj lhs"
                 (state-proof (car (trace-run* (x1 x2) (trace-goal x1=1 (== x1 1)) (== x2 2)))) '((x1=1)))
        (tassert "proof conj rhs"
                 (state-proof (car (trace-run* (x1 x2) (== x1 1) (trace-goal x2=2 (== x2 2))))) '((x2=2)))
        (tassert "proof conde"
                 (map state-proof (trace-run* x1 (conde [(trace-goal x1=1 (== x1 1))] [(== x1 2)]))) '(((x1=1)) ()))

        (tassert "theorem constraint head succeed"
                 (state-proof (car (trace-run* x1 (prove ((x1=1)) (trace-goal x1=1 (== x1 1)))))) '((x1=1)))
        (tassert "theorem constraint head fail"
                 (trace-run* x1 (prove ((x1=2)) (trace-goal x1=1 (== x1 1)))) '())    
        (tassert "theorem trace-conde select branch"
                 (state-proof (car (trace-run* x1 (prove ((x1=2)) (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)]))))) '((x1=2)))
        (tassert "theorem conj of trace-conde"
                 (map state-proof (trace-run* (x1 x2)
                                              (prove ((x1=2) (x2=2))
                                                     (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)])
                                                     (trace-conde [x2=1 (== x2 1)] [x2=2 (== x2 2)])))) '(((x1=2) (x2=2))))
        (tassert "theorem trace-conde nested"
                 (state-proof (car (trace-run* (x1 x2)
                                               (prove ((x1=2 (x2=2)))
                                                      (trace-conde [x1=1 (== x1 1)]
                                                                   [x1=2 (== x1 2)
                                                                         (trace-conde
                                                                          [x2=1 (== x2 1)]
                                                                          [x2=2 (== x2 2)])]))))) '((x1=2 (x2=2))))
       (tassert "theorem trace-conde theorem too shallow fail"
                (trace-run* (x1 x2)
                           (prove ((x1=2))
                                  (trace-conde [x1=1 (== x1 1)]
                                               [x1=2 (== x1 2)
                                                     (trace-conde
                                                      [x2=1 (== x2 1)]
                                                      [x2=2 (== x2 2)])]))) '())
       (tassert "theorem trace-conde theorem too deep fail"
                (trace-run* (x1 x2)
                           (prove ((x1=2 (x2=2)))
                                  (trace-conde [x1=1 (== x1 1)]
                                               [x1=2 (== x1 2)]))) '())
       (tassert "theorem trace-conde theorem prefix succeeds"
                (map state-proof (trace-run* (x1 x2)
                                             (prove ((x1=2 __))
                                                    (trace-conde [x1=1 (== x1 1)]
                                                                 [x1=2 (== x1 2)
                                                                       (trace-conde
                                                                        [x2=1 (== x2 1)]
                                                                        [x2=2 (== x2 2)])])))) '(((x1=2 (x2=1))) ((x1=2 (x2=2)))))
       (tassert "theorem trace-conde theorem prefix leaves wildcard on deep recursion"
                (map
                 state-proof
                 (trace-run*
                  (x1 x2 x3)
                  (prove ((x1=2 __))
                         (trace-conde
                          [x1=1 (== x1 1)]
                          [x1=2 (== x1 2)
                                (trace-conde
                                 [x2=1 (== x2 1)]
                                 [x2=2 (== x2 2)
                                       (trace-conde
                                        [x3=1 (== x3 1)]
                                        [x3=2 (== x3 2)])])]))))
                '(((x1=2 (x2=1))) ((x1=2 (x2=2 (x3=1)))) ((x1=2 (x2=2 (x3=2))))))
       
       (tassert "proofs in lower branches of tree"
                (state-proof
                 (car
                  (trace-run* (x1 x2)
                              (prove ((x1=1))
                                     (trace-conde
                                      [x1=1 (== x1 1)]
                                      [x1=2 (== x1 2)]))
                              (prove ((x2=2))
                                     (trace-conde
                                      [x2=1 (== x2 1)]
                                      [x2=2 (== x2 2)])))))
                '((x1=1) (x2=2)))))))
