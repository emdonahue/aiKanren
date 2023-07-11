(library (listo) ; Relational list library
  (export appendo assoco containso asspo listo for-eacho)
  (import (chezscheme) (ui) (datatypes) (matcho) (negation) (debugging))

  (define (listo l)
    (disj
     (== l '())
     (matcho ([l (a . d)])
	     (listo d))))
  
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

  (define (for-eacho proc xs)
    (assert (procedure? proc))
    (disj (== xs '())
	  (matcho ([xs (x . xs)])
		  ;(printfo "for-eacho~%")
		  (proc x)
		  (for-eacho proc xs))))
  
  (define (assoco x xs o)
    (asspo x xs (lambda (y) (== o y))))

  (define (asspo x xs proc) ; TODO does asspo need an extra argument to succeed if none found? eg disjoin with final goal?
    (matcho ([xs (a-d . t)]) ;TODO merge asspo matchos into single matcho once optimized
	    ;(printfo "asspo2~%")
	    (matcho ([a-d (a . d)])
		    ;(printfo "asspo~%")
		    (conde
		      [(== x a) (proc d)]
		      [(=/= x a) (asspo x t proc)]))))
)
