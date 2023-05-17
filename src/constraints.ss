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
    (constrain
     (fresh ()
       (=/= term absent)
       (fresh (a d)
	 (conde
	   [(=/= term (cons a d))]
	   [(== term (cons a d))
	    (absento a absent)
	    (absento d absent)])))))

  (define (absento2 term absent)
    (noto (presento term absent))))
