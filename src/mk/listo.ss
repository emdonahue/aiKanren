(library (listo) ; Relational list library
  (export appendo assoco containso asspo listo for-eacho membero)
  (import (chezscheme) (datatypes) (matcho) (negation) (debugging) (utils))

  (define (listo l) ; Constrains l to be a proper list.
    (disj
     (== l '())
     (matcho listo ([l (a . d)])
             (listo d))))

  (define (membero x xs) ; Generates all lists xs containing x at least once.
    (matcho ([xs (a . d)])
            (conde
              [(== x a)]
              [(membero x d)])))
  
  (define (appendo h t ht) ; Appends h and t, yielding ht.
    (conde
      [(== h '()) (== t ht)]
      [(matcho appendo ([h (a . d)]
                        [ht (a . es)])
               (== (cons a d) h)
               (== ht (cons a es))
               (appendo d t es))]))

  (define (containso x xs) ; Generates all lists xs containing x, stopping after x is found.
    (matcho containso ([xs (a . d)])
            (conde
              [(== x a)]
              [(=/= x a) (containso x d)])))

  (define (for-eacho proc xs) ; Applies proc to each element of xs.
    (cert (procedure? proc))
    (disj (== xs '())
          (matcho for-eacho ([xs (x . xs^)]) ;TODO test for-eacho with xs^ shadowing xs once matcho identifiers are fixed
                  (proc x)
                  (for-eacho proc xs^))))
  
  (define (assoco x xs o) ;; Unifies x with all keys of alist xs for which o unifies with the value. Analogous to Scheme assoc.
    (asspo x xs (lambda (y) (== o y))))

  (define (asspo x xs proc) ; Binds x to all keys of alist xs for which proc does not fail on the value. Analogous to Scheme assp.

                                        ; TODO does asspo need an extra argument to succeed if none found? eg disjoin with final goal?
    (matcho asspo-list ([xs (a-d . t)]) ;TODO merge asspo matchos into single matcho once optimized
            (matcho asspo-pair ([a-d (a . d)]) ;TODO can alist relations just be constraints if they only return 1 and use constraint semantics to terminate search?
                    (conde
                      [(== x a) (proc d)]
                      [(=/= x a) (asspo x t proc)])))))
