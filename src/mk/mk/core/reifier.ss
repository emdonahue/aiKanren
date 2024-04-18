(library (mk core reifier) ; Responsible for walking and reifying vars
  (export reify reify-var walk walk-var walk-var-val substitution-ref walk-var* reify-answer
          reifier reifier/query reifier/state reifier/pretty-print)
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core streams) (mk core utils) (mk core goals) (mk core mini-substitution))

  (define reifier/query 'query)
  (define reifier/constraints 'constraints)
  (define reifier/pretty-print 'pretty-print)
  (define reifier/state 'state)
  (define reifier (make-parameter reifier/constraints)) ; Defines the type of answers returned by run. May be 'reified for reified query variables or 'state for the entire internal state representation. Defaults to query

  (define reify-answer
    (case-lambda
      [(q s) (reify-answer q s (reifier))]
      [(q s r)
       (cert (state? s))
       (exclusive-cond
        [(eq? r reifier/constraints) (reify s q)]
        [(eq? r reifier/query) (reify-var s q)]
        [(eq? r reifier/state) s]
        [(eq? r reifier/pretty-print) (reify/pretty-print (reify-var s q) s)]
        [(pair? r) (cons (reify-answer q s (car r)) (reify-answer q s (cdr r)))]
        [else (assertion-violation 'reifier "Unrecognized reifier" r)])]))

  (define (reify/pretty-print q s)
    (let ([vs (extract-vars '() q)])
      (cons
       (reify/pretty-print/query q (extract-vars '() q))
       (reify/pretty-print/constraints vs s))))

  (define (reify/pretty-print/query q vs)
    (cond
     [(var? q) (cdr (assq q vs))]
     [(pair? q) (cons (reify/pretty-print/query (car q) vs)
                      (reify/pretty-print/query (cdr q) vs))]
     [else q]))

  (define (reify/pretty-print/constraints vs s)
    '())


  (define (extract-vars vs q)
    (cond
     [(pair? q) (extract-vars (extract-vars vs (car q)) (cdr q))]
     [(var? q)
      (if (assq q vs) vs
          (cons (cons q (string->symbol (string-append "_." (number->string (length vs))))) vs))]
     [(vector? q) (extract-vars vs (vector->list q))]
     [else vs]))
  
  (define reify ;TODO reify vars inside constraints
    (case-lambda
      [(s v) (reify s v '())]
      [(s v vs) 
       (cond
        [(pair? v) (cons (reify s (car v) vs) (reify s (cdr v) vs))]
        [(var? v)
         (if (memq v vs) v
             (let* ([w (walk s v)])
               (if (var? w) w (reify s w (cons v vs)))))]
        [else v])]))

  (define reify-var
    (case-lambda ;TODO parameterize this into reify
      [(s v) (reify-var s v '())]
      [(s v vs) 
       (cond
        [(pair? v) (cons (reify-var s (car v) vs) (reify-var s (cdr v) vs))]
        [(var? v)
         (if (memq v vs) v
             (let ([w (walk-var s v)])
               (if (var? w) w (reify-var s w (cons v vs)))))]
        [else v])]))

  (define (walk s v)
    (cert (state? s)) ; -> (or ground? var? constraint?)
    (let-values ([(binding v) (walk-var-val s v)]) v))

  (define (walk-var s v)
    (cert (state? s)) ; (or ground? var?)
    (let-values ([(lvar val) (walk-var-val s v)])
      (if (goal? val) ; If val is a constraint, the var is still free, so return it.
          lvar val)))

  (define (walk-var-val s v)
    ;; Returns the value or constraints on v, and whatever is the last logic variable in the chain.
    (cert (state? s)) ; -> (or var? ground?) (or (ground? var? constraint?)
    (walk-binding (state-substitution s) v))

  (define (walk-var* s v)
    (cert (or (state? s) (mini-substitution? s))
          (if (state? s) (walk-var s v) (mini-walk s v))))
  
  (define (walk-binding s v)
    ;; Returns the walked value or constraint of v and whatever is the last logic variable in the chain (possibly equal to the value if the var is completely free). If v is ground, it will return two grounds.
    (cert (sbral? s) (not (and (var? v) (zero? (var-id v))))) ; -> (or var? ground?) (or ground? var? constraint?)
    (if (var? v)
        (let ([walked (substitution-ref s v)])
          (exclusive-cond
           [(succeed? walked) (values v v)]
           [(var? walked) (walk-binding s walked)]
           [else (values v walked)]))
        (values v v)))

  (define (substitution-ref s v)
    ;; var-id starts at 1, so for the first var bound, substitution length=1 - varid=1 ==> index=0, which is where it looks up its value. Vars are not stored in the substitution. Instead, their id is used as an index at which to store their value.
    (cert (sbral? s) (var? v))
    (sbral-ref s (fx- (sbral-length s) (var-id v)) succeed)))
