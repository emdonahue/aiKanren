(library (constraints)
  (export =/= booleano presento absento listo finite-domain ==> typeo symbolo)
  (import (chezscheme) (datatypes) (ui) (negation) (state) (matcho))

  (define (=/= lhs rhs)
    (noto (== lhs rhs)))
  
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

  (define (typeo v t?) ; TODO make typo reject immediately if ground term not a type
    (assert (procedure? t?))
    (if (not (var? v))
	(if (t? v) succeed fail)
	(pconstraint
	 v (lambda (s)
	     (let ([v (walk s v)])
	       (cond
		[(var? v) (typeo v t?)]
		[(t? v) succeed]	    
		[else fail]))))))


  (define (symbolo v)
    (typeo v symbol?))

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
