(library (mk interpreter)
  (export evalo initial-env evalo-env synthesizeo
          interpreter/quote interpreter/number interpreter/boolean interpreter/lambda interpreter/lambda/variadic interpreter/lambda/multi-arg interpreter/if interpreter/letrec interpreter/if/non-null)
  (import (chezscheme) (mk core) (mk constraints) (mk lists) (mk tracing))

  (define interpreter/quote (make-parameter #t))
  (define interpreter/number (make-parameter #t))
  (define interpreter/boolean (make-parameter #t))
  (define interpreter/lambda (make-parameter #t))
  (define interpreter/lambda/variadic (make-parameter #t))
  (define interpreter/lambda/multi-arg (make-parameter #t))
  (define interpreter/if (make-parameter #t))
  (define interpreter/if/non-null (make-parameter #t))  
  (define interpreter/letrec (make-parameter #t))
  
  (define empty-env '())
  (define initial-env `((list . (val . (prim . list)))
                        (cons . (val . (prim . cons)))
                        (car . (val . (prim . car)))
                        (cdr . (val . (prim . cdr)))
                        (null? . (val . (prim . null?)))
                        . ,empty-env))
  
  (define evalo
    (case-lambda
      [(expr) (run1 val (evalo expr val))]
      [(expr val) (evalo expr initial-env val)]
      [(expr env val)
       (trace-conde
        [quote (evalo-quote expr env val)]
        [number (evalo-number expr val)]
        [boolean (evalo-boolean expr val)]
        [lookup (symbolo expr) (lookupo expr env val)]
        [lambda (evalo-lambda expr env val)]
        [if (evalo-if expr env val)]
        [apply (evalo-apply expr env val)]
        [letrec (evalo-letrec expr env val)])]))

  (define synthesizeo
    (case-lambda
      [(examples) (synthesizeo examples initial-env)]
      [(examples env)
       (run1 body (synthesizeo body examples))]
      [(body examples env)
       (let* ([params '(a b)]
              [env `((f . (rec . (,params ,body))) . ,env)]) ;TODO generalize from 2 arg fns
        (fold-right conj succeed
                    (map (lambda (e)
                           (evalo body
                                  (fold-right (lambda (p v e) `((,p . (val . ,v)) . ,e)) env params (car e))
                                  (cdr e))) examples)))]))


  ;`(lambda ,(caar args-body) ,(cadr args-body))

  (define (evalo-env expr env)
    ;; Forward direction evalo of expr in env not containing initial-env.
    (run1 val (evalo expr env val)))
  
  (define (evalo-quote expr env val)
    (if (not (interpreter/quote)) fail
     (exist ()
            (== `(quote ,val) expr)
            (absento 'closure val) ; TODO dual absento can potentially be sped up with store-constraint optimizations 
            (absento 'prim val) ; TODO make a higher order absento that applies a fn to all variables. or really just a conjunctive tree map that lets you apply any fn
            (not-shadowedo 'quote env))))

  (define (evalo-number expr val)
    (if (not (interpreter/number)) fail
        (exist () (numbero expr) (== expr val))))

  (define (evalo-boolean expr val)
    (if (not (interpreter/boolean)) fail
        (exist () (booleano val) (== expr val))))
  
  (define (lookupo var env val) ;TODO can lookup be a constraint?
    (asspo var env 
           (lambda (v)
             (conde
               [(== v `(val . ,val))] ; Normal values are tagged as (key . ('val . value))
               [(matcho ([('rec . (args body)) v]) ; Recursive functions are tagged (key . ('rec . (args body))
                         (== val `(closure ,args ,body ,env)))]))))

  (define (evalo-lambda expr env val)
    (if (not (interpreter/lambda)) fail
     (exist ()
            (matcho ([('lambda args body) expr])
                      (== `(closure ,args ,body ,env) val)
                      (constraint
                       (conde
                         [(if (not (interpreter/lambda/variadic)) fail (symbolo args))]
                         [(if (interpreter/lambda/multi-arg)
                              (for-eacho (lambda (x) (symbolo x)) args)
                              (matcho ([(x) args]) (symbolo x)))])))
            (not-shadowedo 'lambda env))))

  (define (evalo-apply expr env val)
    (matcho
     ([(rator . rands) expr])
     (fresh (closure args)
            (evalo rator env closure)
            (conde
              [(matcho ; Normal closure
                ([('closure params body env^) closure])
                (conde
                  [(if (not (interpreter/lambda/variadic)) fail ; Variadic closure
                       (exist ()
                              (symbolo params) 
                              (fresh (arg)
                                     (evalo-listo rands env arg)
                                     (evalo body `((,params . (val . ,arg)) . ,env^) val))))]
                  [(if (interpreter/lambda/multi-arg)
                    (exist ()
                           (for-eacho (lambda (x) (symbolo x)) params)
                           (extend-env params rands env env
                                       (lambda (env^) (evalo body env^ val))))
                    (matcho ([(x) params])
                              (symbolo x)
                              (extend-env params rands env env
                                          (lambda (env^) (evalo body env^ val)))))]))]
              [(matcho ([('prim . prim-id) closure]) ; Primitive operator
                       (evalo-prim prim-id args val)
                       (evalo-listo rands env args))]))))

  (define (evalo-letrec expr env val)
    (if (not (interpreter/letrec)) fail
     (matcho ([('letrec ([name ('lambda args body)]) letrec-body) expr])
               (fresh (closure)
                      (evalo-lambda `(lambda ,args ,body) env closure)
                      (not-shadowedo 'letrec env)
                      (matcho ([('closure args body env^) closure])
                                (evalo letrec-body `((,name . (rec . (,args ,body))) . ,env) val)))
               )))
  
  (define (evalo-prim expr args val)
    (trace-conde
      
      #;
      [(matcho3 ([expr (and . e*)])
               (not-shadowedo 'and env)
               (evalo-and e* env val))]
      [cons (== expr 'cons) (matcho ([(a d) args]
                                      [(a . d) val]))]
      [car (== expr 'car) (matcho ([((a . d)) args])
                                   (== val a))]
      [cdr (== expr 'cdr) (matcho ([((a . d)) args])
                                   (== val d))]
      [null (== expr 'null?) (disj (conj (=/= args '(())) (== val #f))
                                   (conj (== args '(())) (== val #t)))]
      [list (== expr 'list) (== args val)]))
  
  (define (evalo-and e* env val)
    (conde
      [(== e* '()) (== val #t)]))

  (define (evalo-if expr env val)
    (if (not (interpreter/if)) fail
     (matcho ([('if c t f) expr])
             (fresh (tf)
               (if (interpreter/if/non-null) succeed (booleano tf))
               (evalo c env tf)
               (conde
                 [(== tf #f) (evalo f env val)]
                 [(=/= tf #f) (evalo t env val)])))))

  (define (not-shadowedo sym env)
    (noto (asspo sym env (lambda (v) succeed))))

  (define (extend-env params rands env env^ ctn)
    (conde
      [(== params '()) (== rands '()) (ctn env^)]
      [(matcho ([(p . ps) params]
                 [(r . rs) rands])
               (fresh (arg)
                      (evalo r env arg)
                      (extend-env ps rs env `((,p . (val . ,arg)) . ,env^) ctn)))]))

  (define (list-of-symbolso xs) ;TODO replace with for-eacho and rename to for-allo
    (disj (== xs '())
          (matcho ([(a . d) xs])
                  (symbolo a)
                  (list-of-symbolso d))))
  
  (define (evalo-listo expr env val)
    ;; Evaluate all elements of the expr list
    (trace-goal evalo-listo
     (conde
       [(== expr '()) (== val '())]
       [(matcho ([(e . es) expr ]
                 [(v . vs) val])
                (evalo e env v)
                (evalo-listo es env vs))]))))
