(library (listo) ; Relational list library
  (export appendo)
  (import (chezscheme) (ui) (datatypes))

  (define (appendo h t ht)
    (conde
      [(== h '()) (== t ht)]
      ;[(== t '()) (== h ht)]
      [(fresh (a d res)
	 (== (cons a d) h)
	 (== ht (cons a res))
	 (appendo d t res))]))

  #;
  (define (mapo p es o)
    )
)
