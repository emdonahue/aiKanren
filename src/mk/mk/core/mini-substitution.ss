(library (mk core mini-substitution)
  (export mini-walk mini-unify mini-reify mini-diff mini-simplify ->mini-substitution mini-walk-normalized mini-reify-normalized mini-substitution? mini-normalized?)
  (import (chezscheme) (mk core variables) (mk core streams) (mk core goals) (mk core utils))

  (define (->mini-substitution g)
    (cert (==? g))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (mini-substitution? s) (and (list? s) (for-all (lambda (b) (and (pair? b) (var? (car b)))) s)))
  
  (define (mini-walk s v)
    (cert (list? s))
    (if (var? v)
        (let ([b (assq v s)])
          (if b (mini-walk s (cdr b)) v))
        v))

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
    (case-lambda ; -> normalized? walked
      [(s v) (mini-walk-normalized s v s #f)]
      [(s v tail normalized)
       (cond
        [(not (var? v)) (values #t v)]
        [(null? tail) (values normalized v)]
        [(eq? v (caar tail)) (mini-walk-normalized s (cdar tail) s #t)]
        [else (mini-walk-normalized s v (cdr tail) (or normalized (eq? v (cdar tail))))])]))
  
  (define (mini-normalized? s v)
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

  (define (mini-reify-normalized s v)
    (cert (list? s))
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

  (define (mini-diff s^ s)
    ;; Returns a conjunction of == representing the bindings in s^ that are not in s
    (if (eq? s^ s) succeed
        (conj (make-== (caar s^) (cdar s^)) (mini-diff (cdr s^) s))))
  

  (define (extend s x y)
    (cons (cons x y) s)))
