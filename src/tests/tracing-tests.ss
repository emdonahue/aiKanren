(library (tracing-tests)
  (export run-tracing-tests)
  (import (chezscheme) (test-runner) (aikanren) (utils) (debugging) (datatypes) (tracing))

  (define x1 (make-var 1))
  (define x2 (make-var 2))
  
  (define (run-tracing-tests)
    
    (parameterize ([trace-goals #f])
      (tassert "trace ==" (map car (trace-run (x1) (org-untrace (== x1 1)))) '(1))
      (tassert "trace == & ==" (map car (trace-run (x1 x2) (org-untrace (conj* (== x1 1) (== x2 2))))) '((1 2)))
      (tassert "trace == & == depth 1" (map car (trace-run 1 (x1 x2) (== x1 1) (== x2 2))) '((1 2)))
      (tassert "trace == | ==" (map car (trace-run (x1) (org-untrace (conde [(== x1 1)] [(== x1 2)])))) '(1 2))
      (tassert "trace exist" (map car (trace-run (x1) (org-untrace (exist (x2) (== x1 x2) (== x2 1))))) '(1))
      (tassert "trace fresh" (map car (trace-run (x1) (org-untrace  (fresh (x2) (== x1 x2) (== x2 1))))) '(1))
      (tassert "trace matcho" (map car (trace-run (x1) (org-untrace (matcho ([x1 (a . d)]) (== a 1) (== d 2))))) '((1 . 2)))
      (tassert "trace fail if constraint fails" (map car (trace-run (x1) (org-untrace (conde [(== x1 3) (conde [(== x1 1)] [(== x1 2)])] [(== x1 2)])))) '(2))    

      (tassert "proof constraint"
               (cadar (trace-run (x1) (trace-goal x1=1 (== x1 1)))) '((x1=1)))
      (tassert "proof trace-conde"
               (map cadr (trace-run (x1) (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)]))) '(((x1=1)) ((x1=2))))
      (tassert "proof conj"
               (cadar (trace-run (x1 x2) (trace-goal x1=1 (== x1 1)) (trace-goal x2=2 (== x2 2)))) '((x1=1) (x2=2)))
      (tassert "proof conj lhs"
               (cadar (trace-run (x1 x2) (trace-goal x1=1 (== x1 1)) (== x2 2))) '((x1=1)))
      (tassert "proof conj rhs"
               (cadar (trace-run (x1 x2) (== x1 1) (trace-goal x2=2 (== x2 2)))) '((x2=2)))
      (tassert "proof conde"
               (map cadr (trace-run (x1) (conde [(trace-goal x1=1 (== x1 1))] [(== x1 2)]))) '(((x1=1)) ()))
      
      (tassert "theorem constraint head succeed"
               (cadar (trace-run (x1) (prove ((x1=1)) (trace-goal x1=1 (== x1 1))))) '((x1=1)))
      (tassert "theorem constraint head fail"
               (trace-run (x1) (prove ((x1=2)) (trace-goal x1=1 (== x1 1)))) '())    
      (tassert "theorem trace-conde select branch"
               (map cadr (trace-run (x1) (prove ((x1=2)) (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)])))) '(((x1=2))))
      (tassert "theorem conj of trace-conde"
               (cadar (trace-run (x1 x2) (prove ((x1=2) (x2=2))
                                                (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)])
                                                (trace-conde [x2=1 (== x2 1)] [x2=2 (== x2 2)])))) '((x1=2) (x2=2)))
      (tassert "theorem trace-conde nested"
               (map cadr (trace-run (x1 x2)
                                    (prove ((x1=2 (x2=2)))
                                           (trace-conde [x1=1 (== x1 1)]
                                                        [x1=2 (== x1 2)
                                                              (trace-conde
                                                               [x2=1 (== x2 1)]
                                                               [x2=2 (== x2 2)])])))) '(((x1=2 (x2=2)))))
      (tassert "theorem trace-conde theorem too shallow fail"
               (trace-run (x1 x2)
                          (prove ((x1=2))
                                 (trace-conde [x1=1 (== x1 1)]
                                              [x1=2 (== x1 2)
                                                    (trace-conde
                                                     [x2=1 (== x2 1)]
                                                     [x2=2 (== x2 2)])]))) '())
      (tassert "theorem trace-conde theorem too deep fail"
               (trace-run (x1 x2)
                          (prove ((x1=2 (x2=2)))
                                 (trace-conde [x1=1 (== x1 1)]
                                              [x1=2 (== x1 2)]))) '())
      (tassert "theorem trace-conde theorem prefix succeeds"
               (map cadr (trace-run (x1 x2)
                                    (prove ((x1=2 __))
                                           (trace-conde [x1=1 (== x1 1)]
                                                        [x1=2 (== x1 2)
                                                              (trace-conde
                                                               [x2=1 (== x2 1)]
                                                               [x2=2 (== x2 2)])])))) '(((x1=2 (x2=1))) ((x1=2 (x2=2)))))
      (tassert "theorem trace-conde theorem prefix leaves wildcard on deep recursion"
               (map
                cadr
                (trace-run
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


#;    
    (display (values->list (trace-dfs
                            (conj (trace-conde [x1=1 (== x1 1)] [x1=2 (== x1 2)])
                                  (trace-conde [x2=1 (== x2 1)] [x2=2 (== x2 2)]))
                            empty-state empty-package -1 -1 '() '(__) '() succeed)))
      
)))
