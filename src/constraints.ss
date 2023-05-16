(library (constraints)
  (export booleano presento)
  (import (chezscheme) (datatypes) (ui))

  (define (booleano v)
    (constrain
     (conde
       [(== v #t)]
       [(== v #f)])))

  #;
  (define (presento container query)
    (constrain
     (conde
       [(== container query)]
       [(fresh (a d)
	  (== container (cons a d))
	  (conde
	    [(presento a query)]
	    [(presento d query)]))]))
  )

  (define (presento container query)
    (constrain
     (conde
       [(== container query)]
       [(fresh (a d)
	  (== container (cons a d))
	  (conde
	    [(presento a query)]
	    [(presento d query)]))])))
  
)
