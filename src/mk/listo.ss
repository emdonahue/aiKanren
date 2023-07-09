(library (listo) ; Relational list library
  (export appendo assoco containso asspo)
  (import (chezscheme) (ui) (datatypes) (matcho) (negation))

  (define (appendo h t ht)
    (conde
      [(== h '()) (== t ht)]
      [(matcho ([h (a . d)]
		[ht (a . es)])
	       (== (cons a d) h)
	       (== ht (cons a es))
	       (appendo d t es))]))

  (define (containso x xs)
    (matcho ([xs (a . d)])
	    (conde
	      [(== x a)]
	      [(=/= x a) (containso x d)])))
  
  (define (assoco x xs o)
    (asspo x xs (lambda (y) (== o y))))

  (define (asspo x xs proc)
    (matcho ([xs (a-d . t)]) ;TODO merge asspo matchos into single matcho once optimized
	    (matcho ([a-d (a . d)])
		    (conde
		      [(== x a) (proc d)]
		      [(=/= x a) (asspo x t proc)]))))
)
