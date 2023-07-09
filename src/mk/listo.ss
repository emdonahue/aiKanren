(library (listo) ; Relational list library
  (export appendo)
  (import (chezscheme) (ui) (datatypes) (matcho))

  (define (appendo h t ht)
    (conde
      [(== h '()) (== t ht)]
      [(matcho ([h (a . d)]
		[ht (a . es)])
	       (== (cons a d) h)
	       (== ht (cons a es))
	       (appendo d t es))]))
)
