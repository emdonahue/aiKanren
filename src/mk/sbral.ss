;TODO Abstract out some of the math checks for navigating sbral
(library (sbral)
  ;; Skew Binary Random Access List
  (export sbral? sbral-empty sbral-cons sbral-length sbral-ref sbral-set-ref sbral-empty? sbral->alist)
  (import (chezscheme))

  (define-structure (sbral length tree rest))
  (define-structure (sbral-tree size root left right))

  (define sbral-empty (make-sbral 0 (make-sbral-tree 0 'empty 'empty 'empty) '())) ; TODO put the 0 somewhere else so sbral is more aesthetic when printed

  (define (sbral-empty? s) (eq? s sbral-empty))
  
  (define (sbral-cons e s)
    ;; If the first two existing trees are equal in size, merge them into a balanced binary tree with the new element as root.
    (if (fx= (sbral-tree-length s) (sbral-tree-length (sbral-rest s)))
	(let* ([rest (sbral-rest s)]
	       [tlen (fx1+ (fx+ (sbral-tree-length s) (sbral-tree-length rest)))])
	  (make-sbral	   
	   (fx+ tlen (sbral-length (sbral-rest rest)))
	   (make-sbral-tree tlen e (sbral-tree s) (sbral-tree rest))
	   (sbral-rest rest)))
	;; Otherwise, just tack the new element onto the front as a 1-depth tree.
	(make-sbral (fx1+ (sbral-length s)) e s)))

  (define (sbral-ref s n default)    
    (cond
     [(or (fx< n 0) (fx<= (sbral-length s) n)) default]
     [(fx< n (sbral-tree-length s)) (sbral-tree-ref (sbral-tree s) n)]
     [else (sbral-ref (sbral-rest s) (fx- n (sbral-tree-length s)) default)]))
  
  (define (sbral-set-ref s n elt default)
    (assert (and (sbral? s) (fx< n (sbral-length s))))
    (cond
     [(fx< n -1) (sbral-set-ref (sbral-cons default s) (fx1+ n) elt default)] ; Pack empty indices with default.
     [(fx= n -1) (sbral-cons elt s)]
     [else (_sbral-set-ref s n elt)]))

  (define (_sbral-set-ref s n elt)
    (if (fx< n (sbral-tree-length s))
	(make-sbral (sbral-length s) (sbral-tree-set-ref (sbral-tree s) n elt) (sbral-rest s))
	(make-sbral (sbral-length s) (sbral-tree s) (_sbral-set-ref (sbral-rest s) (fx- n (sbral-tree-length s)) elt))))

  (define (sbral-tree-length s)
    ;; sbral->number; Length of the initial tree of sbral s.
    (cond
     [(null? s) -1] ; Just a fake tail for sbral-empty, so invalid length.
     [(sbral-tree? (sbral-tree s)) (sbral-tree-size (sbral-tree s))]
     [else 1])) ; The tree is a single value, which is implicitly considered a 1-depth sbral-tree.
  
  (define (sbral-tree-ref t n)
    (cond
     [(fx= 0 n) (sbral-tree-value t)]
     [(fx< n (fxquotient (fx1+ (sbral-tree-size t)) 2)) (sbral-tree-ref (sbral-tree-left t) (fx1- n))]
     [else (sbral-tree-ref (sbral-tree-right t) (fx- n (fxquotient (fx1+ (sbral-tree-size t)) 2)))]))

  (define (sbral-tree-set-ref t n elt)
    (cond
     [(fx= 0 n) (sbral-tree-set-value t elt)]
     [(fx< n (fxquotient (fx1+ (sbral-tree-size t)) 2))
      (make-sbral-tree (sbral-tree-size t) (sbral-tree-root t)
		       (sbral-tree-set-ref (sbral-tree-left t) (fx1- n) elt)
		       (sbral-tree-right t))]
     [else
      (make-sbral-tree (sbral-tree-size t) (sbral-tree-root t) (sbral-tree-left t)
		       (sbral-tree-set-ref (sbral-tree-right t) (fx- n (fxquotient (fx1+ (sbral-tree-size t)) 2)) elt))]))

  (define (sbral-tree-value t)
    (if (sbral-tree? t) (sbral-tree-root t) t))
  
  (define (sbral-tree-set-value t elt)
    (if (sbral-tree? t)
	(make-sbral-tree (sbral-tree-size t) elt (sbral-tree-left t) (sbral-tree-right t))
	elt))

  (define (sbral->alist s)
    ;; Inefficient. Mostly for debugging.
    (map (lambda (i) (cons i (sbral-ref s i (void)))) (iota (sbral-length s)))))
