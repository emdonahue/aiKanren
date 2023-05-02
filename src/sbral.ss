;; Skew Binary Random Access List
(library (sbral)
  (export sbral-empty sbral-cons)
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

  #;(define (sbral-cons2 e s)
    (cond
     [(null? s) (make-sbral e 1 sbral-empty)]
     [(null? (sbral-rest s)) (make-sbral e 2 s)]
     [(= (sbral-length (sbral-tree s)) (sbral-length (sbral-tree (sbral-rest s))))
      (make-sbral
       (make-sbral-tree e (+ ) (sbral-tree s) (sbral-tree (sbral-rest s)))
       (+ 1 (sbral-size s)))]
     ))

  (define (sbral-cons t s)
    (cond
					;[(null? s) (make-sbral t (sbral-tree-length t) s)]
     [(null? s) (make-sbral t 1 s)]
     [(null? (sbral-rest s)) (make-sbral t 2 s)]
     
     
     [(= (sbral-tree-length (sbral-tree s)) (sbral-tree-length (sbral-tree (sbral-rest s)))) 
      (make-sbral
       (make-sbral-tree			
	t					
	(+ (sbral-tree-length (sbral-tree s)) (sbral-tree-length (sbral-tree (sbral-rest s)))) 
	(sbral-tree s)			
	(sbral-tree (sbral-rest s)))
       (+ (+ (sbral-tree-length (sbral-tree s)) (sbral-tree-length (sbral-tree (sbral-rest s)))) (sbral-length (sbral-rest (sbral-rest s))))
       (sbral-rest (sbral-rest s)))]
					;[else (make-sbral t (+ (sbral-tree-length t) (sbral-size s)) s)]
					;[(null? (sbral-rest s)) (make-sbral t 2 s)]
     #;
     [(= (sbral-tree-length s) (sbral-tree-length (sbral-rest s))) ; ;
     (sbral-cons			; ;
     (make-sbral-tree			; ;
     t					; ;
     (+ (sbral-tree-length s) (sbral-tree-length (sbral-rest s))) ; ;
     (sbral-tree s)			; ;
     (sbral-tree (sbral-rest s)))	; ;
     (sbral-rest s))])
    )
  )
