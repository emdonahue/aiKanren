(library (constraints)
  (export booleano presento absento listo finite-domain ==> typeo symbolo)
  (import (chezscheme) (datatypes) (ui) (state))

  (define (booleano v)
    (constrain
     (conde
       [(== v #t)]
       [(== v #f)])))

  #;
  (define (listo l)
    (constrain
     (conde
       [(== l '())]
       [(fresh (a d)
	  (== l (cons a d))
	  (listo d))])))

  (define (listo l)
    (constrain
     (conde
       [(== l '())]
       [(guardo l (lambda (a d)
		    (listo d)))])))

  (define (finite-domain v ds)
    (assert (list? ds))
    (constrain (disj (map (lambda (d) (== v d)) ds))))

  (define (==> antecedent consequent)
    (assert (and (goal? antecedent) (goal? consequent)))
    (constrain (conde [consequent] [(noto antecedent)])))

  (define (typeo v t?)
    (assert (procedure? t?))
    (pconstraint
     v (lambda (s)
	 (let ([v (walk s v)])
	   (cond
	    [(var? v) (typeo v t?)]
	    [(t? v) succeed]	    
	    [else fail])))))


  (define (symbolo v)
    (typeo v symbol?))


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
  
  ;;if sum is a number, subtract all other numbers from it and pick two random vars from the other side (+ is assoc)
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
  
  #;
  (define (symbolo v)
    (lambda (s)
      (let ([v (walk s)])
	(cond
	 [(symbol? v) succeed]
	 [(var? v) (symbolo v)]
	 [else fail]))))

  (define (presento term present)
    ;; TODO try making constraint freshes that don't bind any external variables just commit. eg for ground terms. maybe their partner in == is ground or also from a constraint fresh?
    (constrain
     (conde
       [(== term present)]
       [(guardo term
		(lambda (a d)
		  (conde
		   [(presento a present)]
		   [(presento d present)])))])))

  (define (absento term absent)
    (constrain
     (fresh ()
       (=/= term absent)
       (conde
	 [(noto (typeo term pair?))]
	 [(guardo term
		  (lambda (a d)
		    (conj*
		     (absento a absent)
		     (absento d absent))))]))))

  #;
  (define (absento3 term absent)
    (constrain
     (fresh ()
       (=/= term absent)
       (conde
	 [(forall (a d) (=/= term (cons a d)))]
	 [(fresh (a d)
	    (== term (cons a d))
	    (absento a absent)
	    (absento d absent))]))))
#;
    (define (presento2 term absent)
    (constrain
     (conde
       [(== term absent)]
       [(fresh (a d) (== term (cons a d)))
	(forall (a d)
	  (=/= term (cons a d))
	  (noto (absento a absent))
	  (noto (absento d absent)))])))
#;
  (define (absento2 term absent)
    (noto (presento term absent))))
