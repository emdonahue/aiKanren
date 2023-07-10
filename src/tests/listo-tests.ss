(library (listo-tests)
  (export run-listo-tests)
  (import (chezscheme) (test-runner) (aikanren) (datatypes))
  
  (define (run-listo-tests)
    (define x1 (make-var 1))
    
    ;; appendo
    (tassert "append empty" (run1 (x1) (appendo '() '() x1)) '())
    (tassert "append empty head" (run1 (x1) (appendo '(1) '() x1)) '(1))
    (tassert "append empty tail" (run1 (x1) (appendo '() '(1) x1)) '(1))
    (tassert "append empty tail" (run1 (x1) (appendo '() '(1) x1)) '(1))
    (tassert "append lists of 2" (run 4 (x1 x2) (appendo x1 x2 '(1 2))) '((() (1 2)) ((1) (2)) ((1 2) ())))

    ;; assoco
    (tassert "assoco 0" (run* (x1) (assoco 3 '((0 . 1) (1 . 2) (2 . 3)) x1)) '())
    (tassert "assoco 1" (run* (x1) (assoco 1 '((0 . 1) (1 . 2) (2 . 3)) x1)) '(2))
    (tassert "assoco 2" (run* (x1) (assoco 1 '((0 . 1) (1 . 2) (1 . 3)) x1)) '(2))
    (tassert "assoco constraint 0" (run* (x1) (constrain (assoco 3 '((0 . 1) (1 . 2) (2 . 3)) __))) '())
    (tassert "assoco constraint 1" (run* (x1) (constrain (assoco 1 '((0 . 1) (1 . 2) (2 . 3)) __))) `(,x1))
    (tassert "assoco constraint 2" (run* (x1) (constrain (assoco 1 '((0 . 1) (1 . 2) (1 . 3)) __))) `(,x1))
    (tassert "assoco constraint not 0" (run* (x1) (constrain (noto (assoco 3 '((0 . 1) (1 . 2) (2 . 3)) __)))) `(,x1))
    (tassert "assoco constraint not 1" (run* (x1) (constrain (noto (assoco 1 '((0 . 1) (1 . 2) (2 . 3)) __)))) '())
    (tassert "assoco constraint not 2" (run* (x1) (constrain (noto (assoco 1 '((0 . 1) (1 . 2) (1 . 3)) __)))) '())


    ;; asspo
    (tassert "asspo 0" (run* (x1) (asspo 3 '((0 . 1) (1 . 2) (2 . 3)) (lambda (x) (== x x1)))) '())
    (tassert "asspo 1" (run* (x1) (asspo 1 '((0 . 1) (1 . 2) (2 . 3)) (lambda (x) (== x x1)))) '(2))
    (tassert "asspo 2" (run* (x1) (asspo 1 '((0 . 1) (1 . 2) (1 . 3)) (lambda (x) (== x x1)))) '(2))

    ;; for-eacho
    (tassert "for-eacho empty" (run1 (x1) (for-eacho (lambda (x) (== x 1)) x1) (== x1 '())) '())
    (tassert "for-eacho succeed 1" (run1 (x1) (for-eacho (lambda (x) (== x 1)) x1) (== x1 '(1))) '(1))
    (tassert "for-eacho succeed 2" (run1 (x1) (for-eacho (lambda (x) (== x 1)) x1) (== x1 '(1 1))) '(1 1))
    (tassert "for-eacho fail" (run1 (x1) (for-eacho (lambda (x) (== x 1)) x1) (== x1 '(1 2))) (void))
    (tassert "for-eacho commit" (run1 (x1 x2) (for-eacho (lambda (x) (== x 1)) x1) (== x1 `(1 ,x2))) '((1 1) 1))
    ))
