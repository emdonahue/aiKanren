(library (mk core mini-substitution)
  (export mini-walk mini-unify mini-reify mini-diff mini-simplify ->mini-substitution mini-walk-normalized mini-reify-normalized mini-substitution? mini-normalized? mini-unify-substitution mini-reify-substitution mini-substitution? mini-disunify mini-disunify/normalized)
  (import (chezscheme) (mk core variables) (mk core streams) (mk core goals) (mk core utils))
  
  (define (->mini-substitution g)
    (cert (==? g))
    (list (cons (==-lhs g) (==-rhs g))))

  (define mini-substitution? list?)
  
  (define (mini-walk s v)
    (cert (list? s))
    (if (var? v)
        (let ([b (assq v s)])
          (if b (mini-walk s (cdr b)) v))
        v))

  (define (mini-walk-binding s v)
    (let ([b (assq v s)])
      (if (var? (cdr b)) (mini-walk-binding s (cdr b)) b)))

  (define (mini-simplify s x y simplified recheck)
    ;; Unifier that sorts bindings by normalized and unnormalized
    (cert (list? s) (goal? simplified) (goal? recheck)) ; -> mini-substitution simplified-==s recheck-==s
    (let-values ([(x-normalized x) (mini-walk-normalized s x)]
                 [(y-normalized y) (mini-walk-normalized s y)])
      (let ([normalized (and x-normalized y-normalized)])
       (cond
        [(eq? x y) (values s simplified recheck)]
        [(var? x) (extend-simplified s x y simplified recheck normalized)]
        [(var? y) (extend-simplified s y x simplified recheck normalized)]
        [(and (pair? x) (pair? y))
         (let-values ([(s simplified recheck) (mini-simplify s (car x) (car y) simplified recheck)])
           (if (failure? s) (values failure fail fail)
               (mini-simplify s (cdr x) (cdr y) simplified recheck)))]
        [else (values failure fail fail)]))))

  (define (extend-simplified s x y simplified recheck normalized)
    (if normalized
        (values (cons (cons x y) s) (conj (== x y) simplified) recheck)
        (values (cons (cons x y) s) simplified (conj (== x y) recheck))))
  
  (define mini-walk-normalized
    ;; A variable is normalized wrt a mini substitution when it is alone on either lhs or rhs. This means that it is either free (rhs) or bound to whatever it is bound to here in the full substitution (lhs) and we can reason about it without walking it in the state.
    (case-lambda ; -> normalized? walked
      [(s v) (mini-walk-normalized s v s #f)]
      [(s v tail normalized)
       (cond
        [(not (var? v)) (values #t v)] ; Non vars are always normalized
        [(null? tail) (values normalized v)] ; if v not in sub, normalization is whatever we've computed
        [(eq? v (caar tail)) (mini-walk-normalized s (cdar tail) s #t)] ; if we find the value in the mini sub, we know it is bound to whatever it is bound to in the full substitution, hence normalized
        [else (mini-walk-normalized s v (cdr tail) ; v is also normalized if it appears explicitly free in the substitution
                                    (or normalized (eq? v (cdar tail))))])]))
  
  (define (mini-normalized? s v)
    ;; A variable is normalized when it is guaranteed not to be bound to something unknown in the substitution. This happens when it is on the lhs, so we know exactly what it is bound to, or it is the sole rhs, so we know that it has been looked up and found to be free.
    (cert (list? s))
    (if (var? v) (memp (lambda (b) (or (eq? v (car b)) (eq? v (cdr b)))) s) #t))

  (define (mini-reify s v)
    (cert (list? s))
    (exclusive-cond
     [(pair? v) (cons (mini-reify s (car v)) (mini-reify s (cdr v)))]
     [(var? v)
      (let ([v^ (mini-walk s v)])
        (if (eq? v v^) v (mini-reify s v^)))] ;TODO should minireify check eq or var?
     [else v]))

  (define (mini-reify-normalized s v) ;TODO do we need to check sub variables for normalization or just attr vars?
    (cert (list? s)) ;TODO do we need mini-*-normalized anymore?
    (exclusive-cond
     [(pair? v)
      (let-values ([(normalized-lhs reified-lhs) (mini-reify-normalized s (car v))]
                   [(normalized-rhs reified-rhs) (mini-reify-normalized s (cdr v))])
        (values (and normalized-lhs normalized-rhs) (cons reified-lhs reified-rhs)))]
     [(var? v)
      (let-values ([(normalized v) (mini-walk-normalized s v)])
        (if (var? v) (values normalized v)
            (mini-reify-normalized s v)))]
     [else (values #t v)]))

  (define (mini-unify s x y)
    (cert (list? s))
    (let ([x (mini-walk s x)] [y (mini-walk s y)])
      (cond
       [(eq? x y) s]
       [(var? x) (extend s x y)]
       [(var? y) (extend s y x)]
       [(and (pair? x) (pair? y))
        (let ([s (mini-unify s (car x) (car y))])
          (if (failure? s) s (mini-unify s (cdr x) (cdr y))))]
       [else failure])))

  (define (mini-disunify s x y)
    (let-values ([(d n?) (mini-disunify/normalized s x y)]) d))

  (define (mini-disunify/normalized s x y)
    (let-values ([(x-normalized? x) (mini-walk-normalized s x)]
                 [(y-normalized? y) (mini-walk-normalized s y)])
      (let ([normalized? (and x-normalized? y-normalized?)])
       (cond
        [(eq? x y) (values fail normalized?)]
        [(var? x) (values (=/= x y) normalized?)]
        [(var? y) (values (=/= y x) normalized?)]
        [(and (pair? x) (pair? y))
         (let-values ([(d normalized?) (mini-disunify/normalized s (car x) (car y))])
           (if (fail? d)
               (mini-disunify/normalized s (cdr x) (cdr y))
               (values (disj d (=/= (cdr x) (cdr y))) normalized?)))]
        [else (values succeed normalized?)]))))

  (define (mini-diff s^ s)
    ;; Returns a conjunction of == representing the bindings in s^ that are not in s
    (if (eq? s^ s) succeed
        (conj (make-== (caar s^) (cdar s^)) (mini-diff (cdr s^) s))))

  (define (mini-unify-substitution s s^)
    ;; Unify all bindings in s^ into s.
    (if (or (failure? s) (null? s^)) s
        (mini-unify s (caar s^) (cdar s^))))

  (define (mini-reify-substitution s s^)
    ;; Update s^ to contain the same bindings it has but with the newest information reflected in s. Lhs should be walked to their maximum variable, rhs should be reified.
    (fold-left (lambda (r b)
                 (let ([b^ (mini-walk-binding s (car b))])
                   (if (assq (car b^) r) r (cons (cons (car b^) (mini-reify s (cdr b^))) r)))) '() s^))

  (define (extend s x y)
    (cons (cons x y) s)))
