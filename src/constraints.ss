;a;TODO test more efficient constraint stores
(library (constraints)
  (export get-constraint get-constraint-binding add-constraint merge-disequality constraint-disequality run-absento merge-constraint)
  (import (chezscheme) (failure) (var) (datatypes))
  
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

  (define (merge-constraint s v c)
    (assert (and (constraint-store? s) (var? v) (goal? c)))
    (let ([b (get-constraint-binding s v)])
      (if b (update-constraint s b (set-constraint-goal (cdr b) (conj* c (constraint-goal (cdr b)))))
	  (add-constraint s v (set-constraint-goal empty-constraint c))
	  ))
    )
  
  (define (merge-disequality s v d)
    (assert (and (constraint-store? s) (var? v) (disequality? d)))
    (let ([c (get-constraint-binding s v)])
      (if c (update-constraint s c (set-disequality (cdr c) (cons d (constraint-disequality (cdr c)))))
	  (add-constraint s v (set-disequality empty-constraint (cons d empty-disequality)))
	  )))

  (define (run-absento s a)
    (assert (and (state? s) (absento? a))) ; -> state-or-fail?
    (assert #f))
  
)
