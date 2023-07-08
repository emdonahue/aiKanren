(library (constraints)
  (export booleano presento absento listo finite-domain ==> typeo symbolo numbero pairo)
  (import (chezscheme) (datatypes) (ui) (negation) (state) (matcho) (utils))
  
  (define (booleano v)
    (disj (== v #t) (== v #f)))

  (define (listo l)
    (disj
     (== l '())
     (matcho ([l (a . d)])
	     (listo d))))

  (define (finite-domain v ds)
    (assert (list? ds))
    (apply disj* (map (lambda (d) (== v d)) ds)))

  (define (==> antecedent consequent)
    (assert (and (goal? antecedent) (goal? consequent)))
    (disj consequent (noto antecedent)))

  (define (typeo v t?)
    (assert (procedure? t?))
    (if (var? v) (pconstraint
		  v 'typeo (lambda (var val)
				       (if (goal? val) (simplify-typeo val var t?)
					   (typeo val t?))))
	(if (t? v) succeed fail)))

  (define (simplify-typeo c v t?)
    (let ([t (conj-memp c (lambda (t) (and (pconstraint? t) (eq? 'type (pconstraint-type t)) (eq? v (car (pconstraint-vars t))))))])
      (if t (if (eq? (pconstraint-procedure c) (pconstraint-procedure t)) succeed fail) (typeo v t?)))
    #;;TODO have typeo simplify == not simply succeed or fail
    (exclusive-cond
     [(conj? c) (conj (simplify-typeo (conj-lhs c) v t?) (simplify-typeo (conj-rhs c) v t?))]
     [(disj? c) (disj (simplify-typeo (disj-lhs c) v t?) (simplify-typeo (disj-rhs c) v t?))]
     [(noto? c) (noto (simplify-typeo (noto-goal c) v t?))]
     [(==? c) ; Only encountered inside disj or noto, so can't throw the typeo away on success. Can only fail.
      (assert (var? (==-lhs c))) ;== already normalized, so lhs is var
      (if (or (not (eq? (==-lhs c) v)) (var? (==-rhs c))) c (if (t? (==-rhs c)) succeed fail))]
     [(pconstraint? c) (if (eq? (pconstraint-type c) 'typeo) (if (eq? (pconstraint-procedure c) t?) succeed fail) c)]
     [else c]))

  (define (symbolo v)
    (typeo v symbol?))

  (define (numbero v)
    (typeo v number?))
  
  (define (pairo v)
    (typeo v pair?))


  #;
  (define (pluso sum . summands)
    (if (null? summands) succeed
	(let ([vars (filter var? (cons sum summands))])
	  (pconstraint
	   (list-head vars 2)
	   (lambda (s)
	     )))))

  #;
  (define (pluso-sum vars sum summands))
  ;; wakled sum is number
  ;;    one+ walked summand is var
  ;;    no walked summands are 
  
  ;;if sum is a number, subtract all other numbers from it and pick two random vars from the other side ( + is assoc)
  ;; if sum is a var, choose one var from the other side and bunch the numbers up on the front of the var list
  ;; run don the list including sum. walk each var/num. if num add to running count. when we get 2 vars, stop
  ;; walk sum. if var, add to var list. if num, negate and add to cumulative count. when returned, if sum was num, subtract 

  #;
  (define (constrain-ground v lam)
    (constrain-var
     v
     (if (var? v) (constrain-var v lam) (lam v))))

  #;
  (define (constrain-var v lam)
    (make-var-constraint v lam)
    )

  #;
  (define (pluso a b c d)
    (make-var-constraint
     (a b)
     (lambda (s)
       
       ))
    )

  (define (presento present term)
    (disj
     (== term present)
     (matcho ([term (a . d)])
	     (disj
	      (presento present a)
	      (presento present d)))))

  (define (absento absent term)
    (conj*
      (=/= term absent)
      (disj
       (noto (pairo term))
       (matcho ([term (a . d)])
	       (absento absent a)
	       (absento absent d))))))
