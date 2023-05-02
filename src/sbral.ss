;; Skew Binary Random Access List
(library (sbral)
  (export sbral-empty sbral-cons sbral-length)
  (import (chezscheme))

  (define-structure (sbral tree size rest))
  (define-structure (sbral-tree root size left right))

  (define sbral-empty '())

  (define (sbral-length s)
    (if (sbral? s) (sbral-size s) 0))

  (define (sbral-tree-length s)
    (cond
     [(null? s) 0]
     [(sbral-tree? (sbral-tree s)) (sbral-tree-size (sbral-tree s))]
     [else 1]))

  (define (sbral-cons e s)
    (cond
     [(null? s) (make-sbral e 1 s)]
     [(= (sbral-tree-length s) (sbral-tree-length (sbral-rest s)))
      (let* ([rest (sbral-rest s)]
	    [tlen (+ 1 (sbral-tree-length s) (sbral-tree-length rest))])
	  (make-sbral
	   (make-sbral-tree e tlen (sbral-tree s) (sbral-tree rest))
	   (+ tlen (sbral-length (sbral-rest rest)))
	   (sbral-rest rest)))]
     [else (make-sbral e (+ 1 (sbral-length s)) s)])))
