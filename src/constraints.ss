;a;TODO test more efficient constraint stores
(library (constraints)
  (export make-constraint constraint? empty-constraint-store disequality? empty-disequality disequality-car disequality-cdr disequality-null? satisfied satisfied? unsatisfiable unsatisfiable? get-constraint get-constraint-binding add-constraint merge-disequality constraint-disequality make-=/= =/=? =/=-lhs =/=-rhs =/=)
  (import (chezscheme) (failure) (var))

  (define-structure (constraint-store constraints))
  (define-structure (constraint disequality type absento))
  (define empty-constraint (make-constraint '() #f #f))
  (define satisfied (make-constraint 'satisfied '_ '_))
  (define (satisfied? c) (eq? c satisfied)) ;TODO rename constraint so that constraint? can include non-structure elements such as satisfied/unsatisfiable
  (define unsatisfiable (make-constraint 'unsatisfiable '_ '_))
  (define (unsatisfiable? c) (eq? c unsatisfiable))
  (define empty-constraint-store (make-constraint-store '()))
  (define-values (empty-disequality disequality? disequality-car disequality-cdr disequality-null?)
    (values '() list? car cdr null?))
  (define-structure (=/= lhs rhs))

  (define (set-disequality c d)
    (assert (and (constraint? c) (disequality? d)))
    (let ([c (vector-copy c)])
      (set-constraint-disequality! c d) c))

  (define =/= make-=/=)
  
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
