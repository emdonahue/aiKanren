(library (mk constraints)
  (export booleano presento absento finite-domain all-different ==> typeo symbolo numbero pairo)
  (import (chezscheme) (mk core goals) (mk core variables) (mk core state) (mk core matcho) (mk core utils) (mk lists))
  
  (define (booleano v) ; Constrains a term to be either #t or #f.
    (disj (== v #t) (== v #f)))

  (define (finite-domain v ds) ; Constrains v to be one of the elements of ds. ds may contain logic variables.
    (cert (list? ds))
    ;;TODO look into making large con/disjunctions of the same variable gather into a binary tree or something other than a random list and automatically build a decent data structure for it
    (matcho ([(a . d) ds])
            (disj (== v a)
                  (finite-domain v d))))

  (define (all-different diffs)
    ;; Takes a list of values so that the list itself can be of indeterminate length.
    (disj
     (== diffs '())
     (matcho ([(a . d) diffs])
             (for-eacho (lambda (v) (=/= a v)) d)
             (all-different d))))

  (define (==> antecedent consequent) ; Simple implication. Equivalent to (disj (noto antecedent) consequent).
    (cert (goal? antecedent) (goal? consequent))
    ;TODO try ==> as =/=|== in case =/= might be more efficient for attribution/
    (disj (noto antecedent) consequent))
  
  (define (typeo v t?) ; Constrains v to be of type t?, where t? is a type predicate.
    (if (var? v) (pconstraint (list v) type t?) (if (t? v) succeed fail)))

  (define (type var val reducer reducee p)
    (cert (pconstraint? p))
    (let ([t? (pconstraint-data p)])
     (exclusive-cond
      [(succeed? reducee) (typeo val t?)]
      [(pconstraint? reducee) (if (eq? type (pconstraint-procedure reducee))
                                  (values fail fail succeed) ; The solver checks equality, so non equal typeos must fail.
                                  (values reducer reducee succeed))]
      [(matcho? reducee) (exclusive-cond
                          [(eq? pair? t?) (values succeed reducee succeed)]
                          [(or (eq? symbol? t?) (eq? number? t?)) (values fail fail succeed)] ;TODO do constraints need to manage recheck individually or is that just for matcho and disj?
                          [else (values reducer reducee succeed)])]
      [else (assertion-violation 'typeo "Unrecognized constraint type" reducee)])))

  #;
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

  (define (symbolo v) ; Constrains v to be a symbol.
    (typeo v symbol?))

  (define (numbero v) ; Constrains v to be a pair.
    (typeo v number?))
  
  (define (pairo v) ; Constrains v to be a pair.
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

  (define (presento present term) ; Constrains term so that it must contain present. Logical negation of absento.
    (disj
     (== term present)
     (matcho presento ([(a . d) term])
             (disj
              (presento present a)
              (presento present d)))))

  (define (absento absent term) ; Constrains term so that absent cannot appear anywhere within it. Logical negation of presento.
    (conj*
      (=/= term absent)
      (disj
       (noto (pairo term))
       (matcho absento ([(a . d) term])
               (absento absent a)
               (absento absent d))))))
