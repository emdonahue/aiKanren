(import (test-runner) (mk core) (mk constraints))

(test-suite
 reifier

 (parameterize ([reifier reifier/state])
   (tassert "reifier state" (run1 x1 (== x1 1)) state?))

 (parameterize ([reifier (cons reifier/state reifier/state)])
   (tassert "reifier (state . state)" (run1 x1 (== x1 1)) (lambda (a) (and (pair? a) (state? (car a)) (state? (cdr a))))))

 (parameterize ([reifier (list reifier/state reifier/state)])
   (tassert "reifier (state state)" (run1 x1 (== x1 1)) (lambda (a) (and (list? a) (state? (car a)) (state? (cadr a))))))

 (parameterize ([reifier reifier/pretty-print])
   (tassert "reifier var" (run1 (x1 x2) (== x1 x2)) '((_.0 _.0)))
   (tassert "reifier vars" (run1 x1 (fresh (x2 x3) (== x1 (cons x2 x3)))) '((_.0 . _.1)))
   (tassert "reifier =/=" (run1 x1 (=/= x1 1)) '(_.0 (=/= (_.0 1))))
   (tassert "reifier =/=s" (run1 (x1 x2) (=/= x1 1) (=/= x1 x2)) '((_.0 _.1) (=/= (_.0 1) (_.0 _.1))))
   (tassert "reifier sym" (run1 x1 (symbolo x1)) '(_.0 (sym _.0)))
   (tassert "reifier syms" (run1 (x1 x2) (symbolo x1) (symbolo x2)) '((_.0 _.1) (sym _.0 _.1)))
   (tassert "reifier num" (run1 x1 (numbero x1)) '(_.0 (num _.0)))
   (tassert "reifier nums" (run1 (x1 x2) (numbero x1) (numbero x2)) '((_.0 _.1) (num _.0 _.1)))
   (tassert "reifier bool" (run1 x1 (booleano x1)) '(_.0 (bool _.0)))
   (tassert "reifier bools" (run1 (x1 x2) (booleano x1) (booleano x2)) '((_.0 _.1) (bool _.0 _.1)))
   (tassert "reifier fd" (run1 x1 (finite-domain x1 '(1 2 3))) '(_.0 (fd (_.0 (1 2 3)))))
   #;
   (tassert "reifier ad hoc" (with-output-to-string (lambda () (display (run1 x1 (disj (=/= x1 1) (disj (symbolo x1) (matcho absento ([(a . d) x1]))))))))
            "(_.0 ((disj (=/= _.0 1) (disj (#<procedure type at constraints.ss:1478> #<procedure symbol?> (_.0)) (#<procedure absento> (_.0))))))")))
