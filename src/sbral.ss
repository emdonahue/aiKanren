;; Skew Binary Random Access List
(library (sbral)
  (export sbral-empty sbral-cons)
  (import (chezscheme))
  
  (define sbral-empty '())
  (define-structure (sbral-tree root size left right))
  (define-structure (sbral tree size rest))

  (define (sbral-length s)
    (cond
     [(sbral? s) (sbral-size s)]
     [(sbral-tree? s) (sbral-tree-size s)]
     [else 1]))

  (define (sbral-cons e s)
    (cond
     [(null? s) (make-sbral e 1 sbral-empty)]
     )))
