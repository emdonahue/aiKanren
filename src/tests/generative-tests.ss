(library (generative-tests)
  (export run-generative-tests)
  (import (chezscheme) (test-runner) (aikanren))

  (define max-vars 3)
  (define-structure (mk-var id))

  (define (mk-expression e)
    (conde
      [(matcho ([e ('== lhs rhs)]) (mk-term lhs) (mk-term rhs))]))

  (define (mk-term t)
    (membero t (map (lambda (i) (make-mk-var (fx1+ i))) (iota max-vars))))
  
  (define (run-generative-tests)

    (display (run* (q) (mk-expression q)))
    
    ))
