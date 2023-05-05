;;TODO break up streams.ss
(library (streams)
  (export mplus make-unification make-disj run-goal make-runner runner-take make-incomplete set-runner-stream runner-next runner-step runner-null? runner-car runner-pair?)
  (import (chezscheme) (state) (failure))  

  ;; === GOALS ===

  (define-structure (unification lhs rhs))
  (define-structure (conj lhs rhs))
  (define-structure (disj lhs rhs))

  (define (goal? g)
    (or (procedure? g) (unification? g) (conj? g) (disj? g)))

  (define (run-goal g s r)
    (assert (and (goal? g) (stream? s) (runner? r)))
    (cond     
     ;[(disj? g) (mplus (run-goal (disj-lhs g) s r) (run-goal (disj-rhs g) s r))]
     [(procedure? g) (g s r)]
     [(unification? g) (set-runner-stream r (unify s (unification-lhs g) (unification-rhs g)))]
     [else (assert #f)]
     ))

  ;; === STREAMS ===

  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))

  (define complete? pair?) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as a list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (mplus? s) (bind? s) (incomplete? s) (failure? s) (answer? s) (guarded? s) (complete? s)))
  
  (define (mplus lhs rhs)
    (cond
     [(failure? lhs) rhs]
     [(failure? rhs) lhs]
     [(runner? lhs) (set-runner-stream lhs (mplus (runner-stream lhs) rhs))]
     [(answer? lhs) (cons lhs rhs)]
     [(answer? rhs) (cons rhs lhs)]
     [(make-mplus lhs rhs)]))

    #;
  (define (bind g s)
    (cond
     [(null? s) '()]
     [(state? s) (run-goal g s)]
     [(mplus? s) (make-bind g s)]
     [else (assert #f)]))

  #;
  (define-syntax bind*
    (syntax-rules ()
      [(_ s) s]
      [(_ s g0 g ...) (bind* (bind g0 s) g ...)]))

  (define (stream-step s r)
    (assert (and (stream? s) (runner? r)))
    (cond
     [(failure? s) (set-runner-stream r s)]
     [(state? (runner-stream r)) (stream-step failure r)]
     [(incomplete? s) (run-goal (incomplete-goal s) (incomplete-state s) r)]
     [(mplus? s) (mplus (stream-step (mplus-rhs s) r) (mplus-lhs s))]
     [else (assert #f)]))

  ;; === RUNNER ===

  (define-structure (runner stream query tables))
  
  (define (set-runner-stream r s)
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r))
  
  (define (runner-step r)
    (assert (runner? r))
    (stream-step (runner-stream r) r))
  
  (define (runner-null? r)
    (assert (runner? r))
    (failure? (runner-stream r)))
  
  (define (runner-pair? r)
    (assert (runner? r))
    (not (failure? (runner-car r))))
  
  (define (runner-car r)
    (assert (runner? r))
    (cond
     [(answer? (runner-stream r)) (runner-stream r)]
     [(complete? (runner-stream r)) (car (runner-stream r))]
     [else failure]))
  
  (define (runner-next r)
    (assert (runner? r))
    (let ([r (runner-step r)])
      (cond
       [(runner-null? r) (values (void) (void) r)]
       [(runner-pair? r) (values (reify (runner-car r) (runner-query r)) (runner-car r) r)]
       [else (runner-next r)])))
  
  (define (runner-take n r)
    (assert (runner? r))
    (if (zero? n) '()
	(let-values ([(reified state r) (runner-next r)])
	  (if (runner-null? r) '() (cons reified (runner-take (- n 1) r)))))))
