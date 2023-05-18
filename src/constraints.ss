(library (constraints)
  (export booleano presento absento listo finite-domain ==> typeo symbolo)
  (import (chezscheme) (datatypes) (ui) (state))

  (define (booleano v)
    (constrain
     (conde
       [(== v #t)]
       [(== v #f)])))

  (define (listo l)
    (constrain
     (conde
       [(== l '())]
       [(fresh (a d)
	  (== l (cons a d))
	  (listo d))])))

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
    (constrain
     (conde
       [(== term present)]
       [(fresh (a d) ; technically needs a =/= term present, but eval in order so implied if still processing that we failed
	  (== term (cons a d))
	  (conde
	    [(presento a present)]
	    [(presento d present)]))])))

  (define (absento term absent)
    (constrain
     (fresh ()
       (=/= term absent)
       (fresh (a d)
	 (conde
	   [(noto (typeo term pair?))
	    #;
	    (=/= term (cons a d))] ; we should be able to detect that no changes were made to the substitution except to extend it with dummy variables. for a cons, this should fail. it succeeds if term is atomic, bc then it def doesnt equal a cons. since we are =/= a constant, surely no new info should be able to come in, so we should be able to commit now. does not exist some vars st this equality holds. more of a (not (fresh (a d) (== term (cons a d)))). single state semantics turn it into effectively a constraint just like ==. a negated fresh constraint could simplify by running fresh as usual, and flattening the goal to success or failure. any amount of satisfiability fails, and fail is the only thing that returns a blank succeed since theres no info in a fail
	   [(== term (cons a d))
	    (absento a absent)
	    (absento d absent)])))))

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
