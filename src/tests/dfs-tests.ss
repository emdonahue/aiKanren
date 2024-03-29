(import (test-runner) (mk) (utils))

(test-suite
 dfs
 
 (parameterize ([search-strategy 'dfs])
   (tassert "dfs ==" (run1 x1 (== x1 1)) 1)
   (tassert "dfs == & ==" (run1 (x1 x2) (== x1 1) (== x2 2)) '(1 2))
   (tassert "dfs == | ==" (run* x1 (conde [(== x1 1)] [(== x1 2)])) '(1 2))
   (tassert "dfs == | == answers 1" (run1 x1 (conde [(== x1 1)] [(== x1 2)])) 1)
   (tassert "dfs fail | ==" (run* x1 (exist (x2) (== x2 1) (conde [(== x2 1) (== x1 1)] [(== x2 2) (== x1 2)]))) '(1))
   (parameterize ([max-depth 1])        
     (tassert "dfs (|) | == depth 1" (run -1 x1 (conde [(fresh (x2) (conde [(== x1 1)] [(== x1 2)]))] [(== x1 3)])) '(3))
     (tassert "dfs == | (|) depth 1" (run -1 x1 (conde [(== x1 3)] [(fresh (x2) (conde [(== x1 1)] [(== x1 2)]))])) '(3)))
   (tassert "dfs exist" (run1 x1 (exist (x2) (== x1 x2) (== x2 1))) 1)
   (tassert "dfs fresh" (run1 x1 (fresh (x2) (== x1 x2) (== x2 1))) 1)
   (tassert "dfs matcho" (run1 x1 (matcho3 ([x1 (a . d)]) (== a 1) (== d 2))) '(1 . 2))
   (tassert "dfs fail if constraint fails" (run* x1 (conde [(== x1 3) (conde [(== x1 1)] [(== x1 2)])] [(== x1 2)])) '(2)))

 ;; Interleaving search also makes use of depth-limiting, so test that without setting the dfs strategy parameter
 (parameterize ([max-depth 1])        
   (tassert "dfs (|) | == depth 1" (run -1 x1 (conde [(fresh (x2) (conde [(== x1 1)] [(== x1 2)]))] [(== x1 3)])) '(3))
   (tassert "dfs == | (|) depth 1" (run -1 x1 (conde [(== x1 3)] [(fresh (x2) (conde [(== x1 1)] [(== x1 2)]))])) '(3))))
