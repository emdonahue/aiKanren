;; Skew Binary Random Access List

(define sbral-empty '())
(define-structure (sbral-leaf element))
(define-structure (sbral-tree root left right))
(define-structure (sbral tree size rest))

(define (sbral-cons e s)
  (cond
   [(null? s) (make-sbral-leaf e)]
   [(sbral-leaf? s) (make-sbral (make-sbral-leaf e) 2 s)]))
