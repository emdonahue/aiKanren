(import (test-runner) (aikanren) (variables) (goals))

(define-structure (mk-var id))
(define vars (map make-var '(1 2 3)))
(define max-vals 2)
(define max-term-depth 1)
(define max-expr-depth 2)
(define symbols '(one two))

(define (mk-expression e depth)
  (conde
    [(if (zero? depth) fail
         (conde
           [(matcho ([e ('conde lhs rhs)]) (mk-expression lhs (fx1- depth)) (mk-expression rhs (fx1- depth)))]
           [(matcho ([e ('conj lhs rhs)]) (mk-expression lhs (fx1- depth)) (mk-expression rhs (fx1- depth)))]))]
    
    [(matcho ([e ('noto goal)]) (mk-expression/primitive goal))]
    [(mk-expression/primitive e)]))

(define (mk-expression/primitive e)
  (conde
    [(matcho ([e ('== lhs rhs)])
             (conde
               [(mk-var lhs) (mk-term rhs max-term-depth)]
               [(mk-term lhs max-term-depth) (mk-var rhs)]))]
    [(matcho ([e ('numbero var)]) (mk-var var))]
    [(matcho ([e ('symbolo var)]) (mk-var var))]
    [(matcho ([e ('pairo var)]) (mk-var var))]))

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
         [constraint (run* (x y z) (constraint c))]
         [goal+constraint (run* (x y z) (constraint c) c)])
                                        ;(printf "~s~%~s~%~s~%" goal constraint goal+constraint)
    (unless (answers-equal? goal constraint goal+constraint)
      (tassert "Generated test" (list goal constraint goal+constraint) #f))))

(define (answers-equal? g c g+c)
  (and (eq? (null? g) (null? c))
       (eq? (null? g) (null? g+c))
       (for-all (lambda (x y z) ;c only returns 1 answ but the others should be len eq
                  (and (eq? (goal? x) (goal? y)) (eq? (goal? x) (goal? z))
                       (or (goal? x) (and (equal? x y) (equal? x z))))) g c g+c)))

(define (compile-mk g)
  (case (car g)
    [== (== (compile-mk/term (cadr g)) (compile-mk/term (caddr g)))]
    [conj (conj (compile-mk (cadr g)) (compile-mk (caddr g)))]
    [conde (conde (compile-mk (cadr g)) (compile-mk (caddr g)))]
    [noto (noto (compile-mk (cadr g)))]
    [numbero (numbero (compile-mk/term (cadr g)))]
    [symbolo (symbolo (compile-mk/term (cadr g)))]
    [pairo (pairo (compile-mk/term (cadr g)))]
    [else (assertion-violation 'compile-mk "Unrecognized goal" g)]))

(define (compile-mk/term t)
  (cond
   [(mk-var? t) (list-ref vars (mk-var-id t))]
   [(pair? t) (cons (compile-mk/term (car t)) (compile-mk/term (cdr t)))]
   [else t]))

(define (mk-term/presento t depth)
  (if (zero? depth) fail
      (conde
        [(== t '())]
        [(== t 1)]
        [(== t (make-mk-var 0))]
        [(== t 2)]
        [(== t (make-mk-var 1))]
        [(matcho ([t (a . d)]) (mk-term/presento a (fx1- depth)) (mk-term/presento d (fx1- depth)))])))

(define (present? v t)
  (cond
   [(eq? v t) #t]
   [(pair? t) (or (present? v (car t)) (present? v (cdr t)))]
   [else #f]))

(define (handle-run g) (run1 () g))

(define (run-absento-tests)
  (for-each
   (lambda (t)
                                        ;(printf "~s~%" t)
     (if (present? (cadr vars) t)
         (begin
           (tassert "generative presento free succeed" (run1 () (presento (cadr vars) t)) '())
           (tassert "generative not-absento free succeed" (run1 () (noto (absento (cadr vars) t))) '())
           (tassert "generative absento free fail" (run1 () (absento (cadr vars) t) (== (car vars) 1)) (void))
           (tassert "generative not-presento free fail" (run1 () (noto (presento (cadr vars) t)) (== (car vars) 1)) (void)))
         (begin
           (tassert "generative presento free fail" (run1 () (presento (cadr vars) t) (== (car vars) 1) (== (cadr vars) 3)) (void)) ; Since x2 is free, we don't know it's not in the term just because we don't see it. The value it eventually unifies with might be in the term.
           (tassert "generative not absento free fail" t (lambda (t) (run1 () (noto (absento (cadr vars) t)) (== (car vars) 1) (== (cadr vars) 3))) (void))
           (tassert "generative absento free succeed" (run1 () (absento (cadr vars) t) (== (car vars) 1)) '())
           (tassert "generative not presento free succeed" (run1 () (noto (presento (cadr vars) t)) (== (car vars) 1)) '())))
     (if (present? 2 t)
         (begin
           (tassert "generative presento ground succeed" (run1 () (presento 2 t)) '())
           (tassert "generative not absento ground succeed" (run1 () (noto (absento 2 t))) '())
           (tassert "generative absento ground fail" (run1 () (absento 2 t)) (void))
           (tassert "generative not-presento ground fail" (run1 () (noto (presento 2 t))) (void)))
         (begin
           (tassert "generative presento ground fail" (run1 () (presento 2 t) (== (car vars) 1) (== (cadr vars) 3)) (void))
           (tassert "generative not absento ground fail" (run1 () (noto (absento 2 t)) (== (car vars) 1) (== (cadr vars) 3)) (void))
           (tassert "generative absento ground succeed" (run1 () (absento 2 t)) '())
           (tassert "generative not presento ground succeed" (run1 () (noto (presento 2 t))) '()))))
   (map compile-mk/term (run* (q) (mk-term/presento q 3))))
  )

(test-suite
 generative
 
 (run-absento-tests)
 ;;    (for-each run-mk (run* (q) (mk-expression q max-expr-depth)))
 ;;(display (length (run* (q) (mk-expression q max-expr-depth))))
                                        ;(pretty-print (run 100 (q) (mk-expression q max-expr-depth)))
 #;
 (let loop ([r (runner (q) (mk-expression q max-expr-depth))]
 [i 0])
 (let-values ([(a s r) (runner-next r)])
 (when (eq? (mod i 100000) 0) (printf "~s: ~s~%" i a))
 (loop r (fx1+ i))))
 )
