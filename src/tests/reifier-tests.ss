(import (test-runner) (mk core) (mk constraints))

(test-suite
 reifier

 (parameterize ([reifier reifier/state])
   (tassert "reifier state" (run1 x1 (== x1 1)) state?))

 (parameterize ([reifier (cons reifier/state reifier/state)])
   (tassert "reifier (state . state)" (run1 x1 (== x1 1)) (lambda (a) (and (pair? a) (state? (car a)) (state? (cdr a))))))

 (parameterize ([reifier reifier/pretty-print])
   (tassert "reifier var" (run1 (x1 x2) (== x1 x2)) '((_.0 _.0)))
   (tassert "reifier vars" (run1 x1 (fresh (x2 x3) (== x1 (cons x2 x3)))) '((_.0 . _.1)))
   (tassert "reifier =/=" (run1 x1 (=/= x1 1)) '(_.0 (=/= (_.0 . 1))))
   (tassert "reifier =/=s" (run1 (x1 x2) (=/= x1 1) (=/= x1 x2)) '((_.0 _.1) (=/= (_.0 . 1) (_.0 . _.1))))
   (tassert "reifier sym" (run1 x1 (symbolo x1)) '(_.0 (sym _.0)))
   (tassert "reifier syms" (run1 (x1 x2) (symbolo x1) (symbolo x2)) '((_.0 _.1) (sym _.0 _.1)))
   (tassert "reifier num" (run1 x1 (numbero x1)) '(_.0 (num _.0)))
   (tassert "reifier nums" (run1 (x1 x2) (numbero x1) (numbero x2)) '((_.0 _.1) (num _.0 _.1)))
   )

 )
