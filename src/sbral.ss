;TODO Abstract out some of the math checks for navigating sbral
(library (sbral)
  ;; Skew Binary Random Access List
  (export sbral-empty sbral-cons sbral-length sbral-ref sbral-set-ref sbral-empty? sbral->alist)
  (import (chezscheme))

  (define-structure (sbral tree length rest))
  (define-structure (sbral-tree root size left right))

  (define sbral-empty (make-sbral (make-sbral-tree 'empty 0 'empty 'empty) 0 '())) ; TODO put the 0 somewhere else so sbral is more aesthetic when printed

  (define (sbral-empty? s) (eq? s sbral-empty))
  
  (define (sbral-cons e s)
    ;; If the first two existing trees are equal in size, merge them into a balanced binary tree with the new element as root.
    (if (= (sbral-tree-length s) (sbral-tree-length (sbral-rest s)))
	(let* ([rest (sbral-rest s)]
	       [tlen (+ 1 (sbral-tree-length s) (sbral-tree-length rest))])
	  (make-sbral
	   (make-sbral-tree e tlen (sbral-tree s) (sbral-tree rest))
	   (+ tlen (sbral-length (sbral-rest rest)))
	   (sbral-rest rest)))
	;; Otherwise, just tack the new element onto the front as a 1-depth tree.
	(make-sbral e (+ 1 (sbral-length s)) s)))

  (define (sbral-ref s n default)    
    (cond
     [(or (< n 0) (<= (sbral-length s) n)) default]
     [(< n (sbral-tree-length s)) (sbral-tree-ref (sbral-tree s) n)]
     [else (sbral-ref (sbral-rest s) (- n (sbral-tree-length s)) default)]))
  
  (define (sbral-set-ref s n elt default)
    (assert (and (sbral? s) (< n (sbral-length s))))
    (cond
     [(< n -1) (sbral-set-ref (sbral-cons default s) (+ n 1) elt default)] ; Pack empty indices with default.
     [(= n -1) (sbral-cons elt s)]
     [else (_sbral-set-ref s n elt)]))

  (define (_sbral-set-ref s n elt)
    (if (< n (sbral-tree-length s))
	(make-sbral (sbral-tree-set-ref (sbral-tree s) n elt) (sbral-length s) (sbral-rest s))
	(make-sbral (sbral-tree s) (sbral-length s) (_sbral-set-ref (sbral-rest s) (- n (sbral-tree-length s)) elt))))

  (define (sbral-tree-length s)
    ;; sbral->number; Length of the initial tree of sbral s.
    (cond
     [(null? s) -1] ; Just a fake tail for sbral-empty, so invalid length.
     [(sbral-tree? (sbral-tree s)) (sbral-tree-size (sbral-tree s))]
     [else 1])) ; The tree is a single value, which is implicitly considered a 1-depth sbral-tree.
  
  (define (sbral-tree-ref t n)
    (cond
     [(zero? n) (sbral-tree-value t)]
     [(< n (quotient (+ 1 (sbral-tree-size t)) 2)) (sbral-tree-ref (sbral-tree-left t) (- n 1))]
     [else (sbral-tree-ref (sbral-tree-right t) (- n (quotient (+ 1 (sbral-tree-size t)) 2)))]))

  (define (sbral-tree-set-ref t n elt)
    (cond
     [(zero? n) (sbral-tree-set-value t elt)]
     [(< n (quotient (+ 1 (sbral-tree-size t)) 2))
      (make-sbral-tree (sbral-tree-root t) (sbral-tree-size t)
		       (sbral-tree-set-ref (sbral-tree-left t) (- n 1) elt)
		       (sbral-tree-right t))]
     [else
      (make-sbral-tree (sbral-tree-root t) (sbral-tree-size t) (sbral-tree-left t)
		       (sbral-tree-set-ref (sbral-tree-right t) (- n (quotient (+ 1 (sbral-tree-size t)) 2)) elt))]))

  (define (sbral-tree-value t)
    (if (sbral-tree? t) (sbral-tree-root t) t))
  
  (define (sbral-tree-set-value t elt)
    (if (sbral-tree? t)
	(make-sbral-tree elt (sbral-tree-size t) (sbral-tree-left t) (sbral-tree-right t))
	elt))

  (define (sbral->alist s)
    ;; Inefficient. Mostly for debugging.
    (map (lambda (i) (cons i (sbral-ref s i (void)))) (iota (sbral-length s)))))
