;a;TODO test more efficient constraint stores
(library (constraints)
  (export make-constraint empty-constraint-store disequality disequality? empty-disequality disequality-car disequality-cdr satisfied satisfied? unsatisfiable unsatisfiable? get-constraint get-constraint-binding add-constraint merge-disequality constraint-disequality make-=/= =/=? =/=-lhs =/=-rhs)
  (import (chezscheme) (failure) (var))

  (define-structure (constraint-store constraints))
  (define-structure (constraint disequality type absento))
  (define empty-constraint (make-constraint '() #f #f))
  (define satisfied '(satisfied))
  (define (satisfied? c) (eq? c satisfied))
  (define unsatisfiable '(unsatisfiable))
  (define (unsatisfiable? c) (eq? c unsatisfiable))
  (define empty-constraint-store (make-constraint-store '()))
  (define-values (empty-disequality disequality? disequality-car disequality-cdr disequality)
    (values '() pair? car cdr (case-lambda
				[(lhs rhs) (disequality lhs rhs empty-disequality)]
				[(lhs rhs rest) (cons (cons lhs rhs) rest)])))
  (define-structure (=/= lhs rhs))
  
  (define (set-disequality c d)
    (assert (and (constraint? c) (disequality? d)))
    (let ([c (vector-copy c)])
      (set-constraint-disequality! c d) c))
  
  (define (get-constraint-binding s v)
    (assert (and (constraint-store? s) (var? v)))
    (assoc v (constraint-store-constraints s)))

  (define (get-constraint s v default)
    (let  ([b (get-constraint-binding s v)])
      (if b (cdr b) default)))

  (define (add-constraint s v c)
    (assert (and (constraint-store? s) (var? v) (constraint? c)))
    (make-constraint-store (cons (cons v c) (constraint-store-constraints s))))

  (define (update-constraint s v c)
    (assert (and (constraint-store? s) (pair? v) (var? (car v)) (constraint? c)))
    (make-constraint-store (cons (cons (car v) c) (remq v (constraint-store-constraints s)))))

  (define (merge-disequality s v d)
    (assert (and (constraint-store? s) (var? v) (disequality? d)))
    (let ([c (get-constraint-binding s v)])
      (if c (update-constraint s c (set-disequality (cdr c) (cons d (constraint-disequality (cdr c)))))
	  (add-constraint s v (set-disequality empty-constraint (cons d empty-disequality)))
	  )))

)
