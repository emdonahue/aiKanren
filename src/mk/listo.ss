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
          (matcho3 for-eacho ([xs (x . xs)])
                  (proc x)
                  (for-eacho proc xs))))
  
  (define (assoco x xs o) ;; Unifies x with all keys of alist xs for which o unifies with the value. Analogous to Scheme assoc.
    (asspo x xs (lambda (y) (== o y))))

  (define (asspo x xs proc) ; Binds x to all keys of alist xs for which proc does not fail on the value. Analogous to Scheme assp.

                                        
    (matcho3 asspo ([xs ((a . d) . t)]) 
             (conde ;TODO can alist relations just be constraints if they only return 1 and use constraint semantics to terminate search?
               [(== x a) (proc d)]
               [(=/= x a) (asspo x t proc)]))))
