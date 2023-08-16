(library (generative-tests)
  (export run-generative-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes))

  (define-structure (mk-var id))
  (define vars (map make-var '(1 2 3)))
  (define max-vals 2)
  (define max-term-depth 2)
  (define max-expr-depth 3)
  (define symbols '(one two))

  (define (mk-expression e depth)
    (if (zero? depth) fail
     (conde
       [(matcho ([e ('conde lhs rhs)]) (mk-expression rhs (fx1- depth)) (mk-expression rhs (fx1- depth)))]
       [(matcho ([e ('conj lhs rhs)]) (mk-expression rhs (fx1- depth)) (mk-expression rhs (fx1- depth)))]
       [(matcho ([e ('noto goal)]) (mk-expression goal (fx1- depth)))]
       [(matcho ([e ('== lhs rhs)])
		(conde
		  [(mk-var lhs) (mk-term rhs max-term-depth)]
		  [(mk-term lhs max-term-depth) (mk-var rhs)]))])))

  (define (mk-term t depth)
    (if (zero? depth) fail
	(conde
	  [(== t '())]
	  [(matcho ([t (a . d)]) (mk-term a (fx1- depth)) (mk-term d (fx1- depth)))]
	  [(membero t (map fx1+ (iota max-vals)))]
	  [(membero t symbols)]
	  [(mk-var t)])))

  (define (mk-var t)
    (membero t (map make-mk-var (enumerate vars))))

  (define (run-mk g)
    (let* ([c (compile-mk g)]
	   [goal (run* (x y z) c)]
	   [constraint (run* (x y z) (constrain c))]
	   [goal+constraint (run* (x y z) (constrain c) c)])
      (unless (and (eq? (null? goal) (null? constraint)) (eq? (null? goal) (null? goal+constraint)))
	(tassert "Generated test" goal constraint))))

  (define (compile-mk g)
    (case (car g)
      [== (== (compile-mk/term (cadr g)) (compile-mk/term (caddr g)))]
      [conj (conj (compile-mk (cadr g)) (compile-mk (caddr g)))]
      [disj (disj (compile-mk (cadr g)) (compile-mk (caddr g)))]
      [noto (noto (compile-mk (cadr g)))]))

  (define (compile-mk/term t)
    (cond
     [(mk-var? t) (list-ref vars (mk-var-id t))]
     [(pair? t) (cons (compile-mk/term (car t)) (compile-mk/term (cdr t)))]
     [else t]))
  
  (define (run-generative-tests)

    (for-each run-mk (run* (q) (mk-expression q max-expr-depth)))
    
    ))
