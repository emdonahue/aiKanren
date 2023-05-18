(library (constraints)
  (export booleano presento absento listo finite-domain ==>)
  (import (chezscheme) (datatypes) (ui))

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
  
  #;
  (define (symbolo v)
    (adhoc v )
    (lambda (s)
      (let ([v (walk s)])
	(cond
	 [(symbol? v) succeed]
	 [(var? v) (symbolo v)]
	 [else fail]))))
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
	   [(=/= term (cons a d))] ; we should be able to detect that no changes were made to the substitution except to extend it with dummy variables. for a cons, this should fail. it succeeds if term is atomic, bc then it def doesnt equal a cons. since we are =/= a constant, surely no new info should be able to come in, so we should be able to commit now. does not exist some vars st this equality holds. more of a (not (fresh (a d) (== term (cons a d)))). single state semantics turn it into effectively a constraint just like ==. a negated fresh constraint could simplify by running fresh as usual, and flattening the goal to success or failure. any amount of satisfiability fails, and fail is the only thing that returns a blank succeed since theres no info in a fail
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
