(library (constraints)
  (export booleano presento absento finite-domain ==> typeo symbolo numbero pairo)
  (import (chezscheme) (datatypes) (ui) (negation) (state) (matcho) (utils))
  
  (define (booleano v)
    (disj (== v #t) (== v #f)))

  (define (finite-domain v ds)
    (cert (list? ds))
    (apply disj* (map (lambda (d) (== v d)) ds)))

  (define (==> antecedent consequent) ;TODO try ==> as =/=|== in case =/= might be more efficient for attribution/
    (cert (goal? antecedent) (goal? consequent))
    (disj (noto antecedent) consequent))
  
  (define typeo
    (case-lambda
      [(v t?) ; User-facing constraint constructor
	(cert (procedure? t?))
	(if (var? v) (pconstraint (list v) typeo t?) (if (t? v) succeed fail))]
      [(var val t?) (typeo val t?)] ; Internal interface for var/val bindings
      [(var var^ c t?) ; Internal interface for constraints
       (simplify-typeo c var^ t?)]))

  (define (simplify-typeo c v t?)
    (cert (goal? c) (var? v))
    (let ([t (conj-memp c (lambda (t)
			    (and (pconstraint? t)
				 (eq? typeo (pconstraint-procedure t))
				 (eq? v (car (pconstraint-vars t))))))])
      (if t (if (eq? t? (pconstraint-data t)) succeed fail) (typeo v t?)))
    #;;TODO have typeo simplify == not simply succeed or fail
    (exclusive-cond
     [(conj? c) (conj (simplify-typeo (conj-lhs c) v t?) (simplify-typeo (conj-rhs c) v t?))]
     [(disj? c) (disj (simplify-typeo (disj-lhs c) v t?) (simplify-typeo (disj-rhs c) v t?))]
     [(noto? c) (noto (simplify-typeo (noto-goal c) v t?))]
     [(==? c) ; Only encountered inside disj or noto, so can't throw the typeo away on success. Can only fail.
      (cert (var? (==-lhs c))) ;== already normalized, so lhs is var
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
     (matcho presento ([term (a . d)])
	     (disj
	      (presento present a)
	      (presento present d)))))

  (define (absento absent term) ;TODO create defconstraint that tags any matchos returned with the function pointer so they can dedup themselves
    (conj*
      (=/= term absent)
      (disj
       (noto (pairo term))
       (matcho absento ([term (a . d)])
	       (absento absent a)
	       (absento absent d))))))
