(library (constraints)
  (export booleano presento absento)
  (import (chezscheme) (datatypes) (ui))

  (define (booleano v)
    (constrain
     (conde
       [(== v #t)]
       [(== v #f)])))

  (define (presento term present)
    (constrain
     (conde
       [(== term present)]
       [(fresh (a d)
	  (== term (cons a d))
	  (conde
	    [(presento a present)]
	    [(presento d present)]))])))

  (define (absento term absent)
    (noto (presento term absent))))
