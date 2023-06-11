;;TODO perhaps all constraint lookups receive pointers to a single store so that we can cheeply copy pointers to different attributed variables but only remove and apply the constraint once instead of copying the constraint and applying it many times
;;TODO == and =/= have different attributed variables, so each variable should store two lists. moreover, == are a superset of =/= so == list can just store the diff and then append them
(library (store) ; Constraint store
  (export get-constraint add-constraint remove-constraint reify-constraint)
  (import (chezscheme) (datatypes))

  (define (get-constraint s v)
    (let  ([b (get-constraint-binding s v)])
      (if b (cdr b) succeed)))

  (define (add-constraint s v c)
    (let ([b (get-constraint-binding s v)])
      (if b (update-constraint s b (conj c (cdr b)))
	  (insert-constraint s v c))))

  (define (get-constraint-binding s v)
    ;; Since we are working with an a-list, we can cheat and work directly on the pairs rather than abstracting the store entirely in terms of variable key and constraint value.
    (assoc v (constraint-store-constraints s)))

  (define (insert-constraint s v c)
    (make-constraint-store (cons (cons v c) (constraint-store-constraints s))))

  (define (update-constraint s v c)
    (make-constraint-store (cons (cons (car v) c) (remq v (constraint-store-constraints s)))))

  (define (remove-constraint s v)
    (make-constraint-store (remq (assoc v (constraint-store-constraints s)) (constraint-store-constraints s))))

  (define (reify-constraint s v)
    (if (not (var? v)) v
	(let ([c (get-constraint s v)])
	  (if (succeed? c) v c)))))
