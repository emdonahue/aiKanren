(library (mk core reifier) ; Responsible for walking and reifying vars
  (export reify reify-var reify-answer
          reifier reifier/query reifier/state reifier/pretty-print reifier/constraints)
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core streams) (mk core utils) (mk core goals) (mk core mini-substitution) (mk core walk) (mk core matcho))

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
        [(null? r) '()]
        [else (assertion-violation 'reifier "Unrecognized reifier" r)])]))

  (define (reify/pretty-print q s)
    (let ([vs (extract-vars '() q)])
      (reify/pretty-print/vars
       (cons q (reify/pretty-print/constraints vs s)) vs)))

  (define (reify/pretty-print/vars q vs)
    (cond
     [(var? q) (cdr (assq q vs))]
     [(pair? q) (cons (reify/pretty-print/vars (car q) vs)
                      (reify/pretty-print/vars (cdr q) vs))]
     [(matcho? q)
      (reify/pretty-print/vars
       (list (matcho-ctn q) (matcho-attributed-vars q)) vs)]
     [(pconstraint? q)
      (reify/pretty-print/vars
       (list (pconstraint-procedure q) (pconstraint-data q) (pconstraint-vars q)) vs)]
     [(=/=? q) (list '=/= (reify/pretty-print/vars (=/=-lhs q) vs)
                     (reify/pretty-print/vars (=/=-rhs q) vs))]
     [(vector? q) (reify/pretty-print/vars (vector->list q) vs)]
     [else q]))

  (define (reify/pretty-print/constraints vs s)
    (let* ([cs (fold-left conj succeed (filter goal? (map (lambda (v) (reify s (car v))) vs)))]
           [vs (extract-vars vs cs)])
      (let*-values ([(ds cs) (conj-partition =/=? cs)]
                    [(syms cs) (conj-partition symbolo? cs)]
                    [(nums cs) (conj-partition numbero? cs)]
                    [(bools cs) (conj-partition booleano? cs)]
                    [(fds cs) (conj-partition finite-domain? cs)]
                    [(cs) (conj-filter (lambda (c) (not (proxy? c))) cs)])
        (append
         (if (succeed? ds) '()
             (list (cons '=/= (conj-fold (lambda (ds d) (cons (list (=/=-lhs d) (=/=-rhs d)) ds)) '() ds))))
         (if (succeed? syms) '()
             (list (cons 'sym (conj-fold (lambda (cs c) (cons (car (pconstraint-vars c)) cs)) '() syms))))
         (if (succeed? nums) '()
             (list (cons 'num (conj-fold (lambda (cs c) (cons (car (pconstraint-vars c)) cs)) '() nums))))
         (if (succeed? bools) '()
             (list (cons 'bool (conj-fold (lambda (cs c) (cons (==-lhs (disj-lhs c)) cs)) '() bools))))
         (if (succeed? fds) '()
             (list (cons 'fd (conj-fold
                              (lambda (cs c)
                                (let ([ds (disj->list c)])
                                  (cons (cons (==-lhs (car ds)) (list (map ==-rhs ds))) cs))) '() fds))))
         (if (succeed? cs) '()
             (list (conj-fold (lambda (cs c) (cons c cs)) '() cs)))))))


  (define (symbolo? c) ; TODO make pconstraint checks in reifier more precise by factoring out internals to be shared 
    (and (pconstraint? c) (eq? (pconstraint-data c) symbol?)))

  (define (numbero? c) ; TODO make pconstraint checks in reifier more precise by factoring out internals to be shared 
    (and (pconstraint? c) (eq? (pconstraint-data c) number?)))

  (define (booleano? c)
    (and (disj? c)
         (let ([lhs (disj-lhs c)]
               [rhs (disj-rhs c)])
           (and 
            (==? lhs)
            (==? rhs)
            (equal? (==-lhs lhs) (==-lhs rhs))
            (or (and (eq? (==-rhs lhs) #t) (eq? (==-rhs rhs) #f))
                (and (eq? (==-rhs lhs) #f) (eq? (==-rhs rhs) #t)))))))

  (define (finite-domain? c)
    (and (disj? c)
         (let ([ds (disj->list c)])
           (and (for-all (lambda (d) (and (==? d) (eq? (==-lhs (car ds)) (==-lhs d)))) ds)))))
  
  (define (extract-vars vs q)
    (cond
     [(pair? q) (extract-vars (extract-vars vs (car q)) (cdr q))]
     [(var? q)
      (if (assq q vs) vs
          (cons (cons q (string->symbol (string-append "_." (number->string (length vs))))) vs))]
     [(matcho? q) (extract-vars vs (matcho-attributed-vars q))]
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
        [else v])])))
