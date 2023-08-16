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
       [(matcho ([e ('noto goal)]) (mk-expression/primitive goal))]
       [(mk-expression/primitive e)])))

  (define (mk-expression/primitive e)
    (conde
      [(matcho ([e ('== lhs rhs)])
	       (conde
		 [(mk-var lhs) (mk-term rhs max-term-depth)]
		 [(mk-term lhs max-term-depth) (mk-var rhs)]))]
      [(matcho ([e ('numbero var)]) (mk-var var))]
      [(matcho ([e ('symbolo var)]) (mk-var var))]))

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
					;(printf "~s~%~s~%~s~%" goal constraint goal+constraint)
      (unless (answers-equal? goal constraint goal+constraint)
	(tassert "Generated test" (list goal constraint goal+constraint) #f))))

  (define (answers-equal? g c g+c)
    (and (eq? (null? g) (null? c))
	 (eq? (null? g) (null? g+c))
	 (for-all (lambda (x y z)
		    (and (eq? (goal? x) (goal? y)) (eq? (goal? x) (goal? z))
			 (or (goal? x) (and (equal? x y) (equal? x z))))) g c g+c)))

  (define (compile-mk g)
    (case (car g)
      [== (== (compile-mk/term (cadr g)) (compile-mk/term (caddr g)))]
      [conj (conj (compile-mk (cadr g)) (compile-mk (caddr g)))]
      [disj (disj (compile-mk (cadr g)) (compile-mk (caddr g)))]
      [noto (noto (compile-mk (cadr g)))]
      [numbero (numbero (compile-mk/term (cadr g)))]
      [symbolo (symbolo (compile-mk/term (cadr g)))]))

  (define (compile-mk/term t)
    (cond
     [(mk-var? t) (list-ref vars (mk-var-id t))]
     [(pair? t) (cons (compile-mk/term (car t)) (compile-mk/term (cdr t)))]
     [else t]))
  
  (define (run-generative-tests)

    (for-each run-mk (run 10 (q) (mk-expression q max-expr-depth)))
    
    ))
