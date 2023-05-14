;TODO delete datatypes.ss
(library (datatypes)
  (export make-runner set-runner-stream runner? runner-stream runner-query runner-package
	  package? empty-package
	  make-==  make-incomplete complete? stream? complete complete? complete-car complete-cdr incomplete? incomplete-goal incomplete-state mplus? mplus-lhs mplus-rhs
	  make-var var? var-id var-equal?
	  succeed fail succeed? fail?
	  make-state empty-state state? set-state-substitution state-constraints state-substitution state-varid increment-varid instantiate-var set-state-constraints copy-varid
	  failure failure? guarded? answer? state-or-failure?
	  make-constraint constraint? empty-constraint-store constraint-store? constraint-goal constraint-store-constraints make-constraint-store set-constraint-goal
	  make-substitution empty-substitution substitution-dict substitution?
	  make-== ==? ==-lhs ==-rhs disj make-disj disj* normalized-disj normalized-disj* disj? disj-car disj-cdr disj-disjuncts goal? fresh? make-conj conj conj* normalized-conj normalized-conj* conjunctive-normal-form conj? conj-car conj-cdr conj-conjuncts == make-noto noto? noto-goal)
  (import (chezscheme) (sbral))

  ;; === RUNNER ===
  (define-structure (runner stream query package))
  
  (define (set-runner-stream r s)
    (assert (and (runner? r) (not (runner? s))))
    (let ([r (vector-copy r)])
      (set-runner-stream! r s) r))

  ;; === PACKAGE ===  
  (define-structure (package tables))
  (define empty-package (make-package '()))
  
  ;; === VAR ===
  (define-structure (var id)) ;TODO make the var tag a unique object to avoid unifying with a (var _) vector and confusing it for a real var
  (define var-equal? equal?)
  
  ;; === STREAMS ===
  (define failure '())
  (define failure? null?)
  (define-structure (mplus lhs rhs))
  (define-structure (bind goal stream))
  (define-structure (incomplete goal state))
  (define-values (complete complete? complete-car complete-cdr) (values cons pair? car cdr)) ; A complete stream is one with at least one answer and either more answers or a incomplete stream. It is represented as an improper list of answer?s, possibly with an improper stream tail.
  
  (define (stream? s)
    (or (failure? s) (mplus? s) (bind? s) (incomplete? s) (answer? s) (guarded? s) (complete? s)))
  
  ;; === GOALS ===
  
  (define-values (succeed fail) (values '(succeed) '(fail)))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))

    ;; === CONSTRAINT STORE ===
  (define-structure (constraint-store constraints)) ; Constraints are represented as a list of pairs in which car is the attributed variable and cdr is the goal representing the constraint
  (define-structure (constraint goal))
  (define empty-constraint-store (make-constraint-store '()))
  (define (set-constraint-goal c g)
    (assert (and (constraint? c) (goal? g)))
    (let ([c (vector-copy c)])
      (set-constraint-goal! c g) c))

    ;; === SUBSTITUTION ===
  (define-structure (substitution dict))
  (define empty-substitution (make-substitution sbral-empty))
  
  ;; === STATE ===
  (define-structure (state substitution constraints guards pseudocounts varid))
  (define empty-state (make-state empty-substitution empty-constraint-store '() #f 1))

  (define (set-state-substitution s substitution)
    (if (not (failure? substitution))
	(let ([s (vector-copy s)])
	  (set-state-substitution! s substitution) s) substitution))

  (define (set-state-constraints s c)
    (if (not (failure? c))
	(let ([s (vector-copy s)])
	  (set-state-constraints! s c) s) c))

  (define (increment-varid s)
    (assert (state? s))
    (let ([s (vector-copy s)])
      (set-state-varid! s (+ 1 (state-varid s))) s))

  (define (copy-varid from to)
    (assert (and (state? to) (stream? from)))
    (if (failure? from) from
	(let ([to (vector-copy to)])
	  (set-state-varid!
	   to
	   (cond
	    [(state? from) (state-varid from)]
	    [else (state-varid to)])) to)))

  (define (state-or-failure? s) (or (state? s) (failure? s)))

  (define (instantiate-var s)
    (values (make-var (state-varid s)) (increment-varid s)))

  ;; === STREAMS ===

  (define (answer? s)
    (and (state? s) (null? (state-guards s))))
  
  (define (guarded? s)
    (and (state? s) (not (null? (state-guards s)))))

  ;; === GOALS ===
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints
  (define-structure (conj conjuncts))
  (define-structure (disj disjuncts))
  (define-structure (noto goal)) ; Negated goal

  (define == make-==)

  (define fresh? procedure?) ; Fresh goals are currently represented by their raw continuation.
  
  (define (goal? g)
    (or (fresh? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (noto? g) (constraint? g)))

  (define (conj conjuncts)
    (assert (list? conjuncts))
    ;;TODO move failures to the front so they run first, but do not fail immediately in case we need to negate
    ;;TODO append subconjuncts into a flat list
    (cond
     [(null? conjuncts) succeed]
     [(null? (cdr conjuncts)) (car conjuncts)]
     [else (make-conj conjuncts)]))
  
  (define (conj* . conjs)
    (conj conjs))

  (define (normalized-conj c)
    (let ([c (normalize-conj c)])
      (if (fail? c) fail (conj c))))
  
  (define (normalize-conj cs)
    (cond
     [(null? cs) '()]
     [(fail? (car cs)) fail]
     [(succeed? (car cs)) (cdr cs)]
     [else
      (let ([rest (normalize-conj (cdr cs))])
	(cond
	 [(fail? rest) fail]
	 [(conj? (car cs)) (append (conj-conjuncts (car cs)) rest)]
	 [else (cons (car cs) rest)]))]))

  (define (normalized-conj* . conjuncts)
    (normalized-conj conjuncts))

  (define (cartesian-product ls)
    (fold-right
     (lambda (a b) 
       (apply append
	      (map (lambda (x)
		     (map (lambda (y)
			    (list x y)) (cadr ls)))
		   (car ls)))) '() ls))
  
  
  (define (conjunctive-normal-form g)
    (assert (goal? g))
    (cond
      [(conj? g) (normalized-conj (map conjunctive-normal-form (conj-conjuncts g)))]
      [(disj? g) (normalized-conj
		  (map normalized-disj
		       (cartesian-product
			(map (lambda (g) (if (conj? g) (conj-conjuncts g) (list g)))
			     (disj-disjuncts g)))))]
      [else g]
      )
    )
  
  (define (conj-car c)
    (assert (conj? c))
    (car (conj-conjuncts c)))

  (define (conj-cdr c)
    (assert (conj? c))
    (conj (cdr (conj-conjuncts c))))

  (define (disj disjuncts)
    (assert (list? disjuncts))
    ;;TODO move successes to front of disj so they turn into failures if negated
    (cond
     [(null? disjuncts) fail]
     [(null? (cdr disjuncts)) (car disjuncts)]
     [else (make-disj disjuncts)]))

  (define (disj* . disjuncts)
    (disj disjuncts))

  (define (normalized-disj d)
    (let ([d (normalize-disj d)])
      (if (succeed? d) succeed (disj d))))

  (define (normalized-disj* . disjuncts)
    (normalized-disj disjuncts))

  (define (normalize-disj ds)
    (cond
     [(null? ds) '()]
     [(succeed? (car ds)) succeed]
     [(fail? (car ds)) (cdr ds)]
     [else
      (let ([rest (normalize-disj (cdr ds))])
	(cond
	 [(succeed? rest) succeed]
	 [(disj? (car ds)) (append (disj-disjuncts (car ds)) rest)]
	 [else (cons (car ds) rest)]))]))

  (define (disj-car d)
    (car (disj-disjuncts d)))

  (define (disj-cdr d)
    (disj (cdr (disj-disjuncts d)))))
