(library (substitution)
  (export empty-substitution walk unify make-var var? var-id extend print-substitution)
  (import (chezscheme) (sbral) (datatypes))

  (define unbound (vector 'unbound)) ; Internal placeholder for unbound variables in the substitution.
  (define (unbound? v) (eq? unbound v))

  (define (walk s v)
    (if (var? v)
	(let* ([dict (substitution-dict s)]
	       [walked (sbral-ref dict (- (sbral-length dict) (var-id v)) unbound)]) ; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
	  (if (unbound? walked) v (walk s walked)))
	v))


  (define (extend s x y)
    (values
     (make-substitution
      (sbral-set-ref
       (substitution-dict s)
       (- (sbral-length (substitution-dict s)) (var-id x)) y unbound)) (== x y)))

  (define (print-substitution s)
    (let ([sbral (substitution-dict s)])
      (map (lambda (p) (cons (make-var (- (sbral-length sbral) (car p))) (cdr p))) (sbral->alist sbral)))))
