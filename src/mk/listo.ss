(library (listo) ; Relational list library
  (export appendo assoco containso asspo listo for-eacho membero)
  (import (chezscheme) (goals) (matcho) (negation) (debugging) (utils))

  (define (listo l) ; Constrains l to be a proper list.
    (disj
     (== l '())
     (matcho3 listo ([l (a . d)])
             (listo d))))

  (define (membero x xs) ; Generates all lists xs containing x at least once.
    (matcho3 ([xs (a . d)])
            (conde
              [(== x a)]
              [(membero x d)])))
  
  (define (appendo h t ht) ; Appends h and t, yielding ht.
    (conde
      [(== h '()) (== t ht)]
      [(matcho3 appendo ([h (a . d)]
                        [ht (a . es)])
               (== (cons a d) h)
               (== ht (cons a es))
               (appendo d t es))]))

  (define (containso x xs) ; Generates all lists xs containing x, stopping after x is found.
    (matcho3 containso ([xs (a . d)])
            (conde
              [(== x a)]
              [(=/= x a) (containso x d)])))

  (define (for-eacho proc xs) ; Applies proc to each element of xs.
    (cert (procedure? proc))
    (disj (== xs '())
          (matcho3 for-eacho ([xs (x . xs^)]) ;TODO test for-eacho with xs^ shadowing xs once match identifiers are fixed
                  (proc x)
                  (for-eacho proc xs^))))
  
  (define (assoco x xs o) ;; Unifies x with all keys of alist xs for which o unifies with the value. Analogous to Scheme assoc.
    (asspo x xs (lambda (y) (== o y))))

  (define (asspo x xs proc) ; Binds x to all keys of alist xs for which proc does not fail on the value. Analogous to Scheme assp.

                                        ; TODO does asspo need an extra argument to succeed if none found? eg disjoin with final goal?
    (matcho3 asspo-list ([xs (a-d . t)]) ;TODO merge asspo matches into single match once optimized
            (matcho3 asspo-pair ([a-d (a . d)]) ;TODO can alist relations just be constraints if they only return 1 and use constraint semantics to terminate search?
                    (conde
                      [(== x a) (proc d)]
                      [(=/= x a) (asspo x t proc)])))))
