;; Skew Binary Random Access List
(library (sbral)
  (export sbral-empty sbral-cons sbral-length)
  (import (chezscheme))

  (define-structure (sbral tree size rest))
  (define-structure (sbral-tree root size left right))

  (define sbral-empty (make-sbral (make-sbral-tree #f 0 #f #f) 0 '()))

  (define (sbral-length s)
    (if (sbral? s) (sbral-size s) 0))

  (define (sbral-tree-length s)
    (cond
     [(null? s) -1] ; Just a fake tail for empty-sbral, so invalid length.
     [(sbral-tree? (sbral-tree s)) (sbral-tree-size (sbral-tree s))]
     [else 1]))

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
	(make-sbral e (+ 1 (sbral-length s)) s))


    ))
