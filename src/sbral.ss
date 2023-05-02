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
     [(sbral-tree? s) (sbral-tree-size s)]
     [else 1]))

  (define (sbral-cons e s)
    (cond
     [(null? s) (make-sbral e 1 s)]
     [(null? (sbral-rest s)) (make-sbral e (+ 1 (sbral-length s)) s)]


     [(= (sbral-tree-length (sbral-tree s)) (sbral-tree-length (sbral-tree (sbral-rest s))))
      (let* ([rest (sbral-rest s)]
	    [t1 (sbral-tree s)]
	    [t2 (sbral-tree rest)]
	    [tlen (+ 1 (sbral-tree-length t1) (sbral-tree-length t2))])
	  (make-sbral
	   (make-sbral-tree e tlen t1 t2)
	   (+ tlen (sbral-length (sbral-rest rest)))
	   (sbral-rest rest)))]))
  )
