(library (ui)
  (export == conde run fresh runner runner-next runner-step runner-null? runner-take)
  (import (chezscheme) (streams) (state) (runner) (running) (goals))

  (define (== x y)
    (make-unification x y))

  (define (conde x y)
    (make-disj x y))
  
 (define-syntax fresh
   (syntax-rules ()
     [(_ () g ...)
      (lambda (start-state r)
	(set-runner-stream r (make-incomplete (conj* g ...) start-state)))]
     [(_ (q ...) g ...)
      (lambda (start-state r)
	(fresh-vars
	 start-state end-state (q ...)
	 (set-runner-stream r (make-incomplete (conj* g ...) end-state))))]))

  (define-syntax runner
    (syntax-rules ()
      [(_ (q) g ...)
       (fresh-vars
	empty-state start-state (q)
	(build-runner start-state q g ...))]
      [(_ (q0 q ...) g ...)
       (fresh-vars
	empty-state start-state (q0 q ...)
	(build-runner start-state (list q0 q ...) g ...))]))
  
  (define-syntax run
    (syntax-rules ()
      ((_ n (q ...) g ...)
       (runner-take n (runner (q ...) g ...)))))

  (define-syntax run*
    (syntax-rules ()
      ((_ (q ...) g ...) (run -1 (q ...) g ...))))

  ;; === UTILITIES ===

    (define-syntax fresh-vars
    (syntax-rules ()
      [(_ start-state end-state (q) body ...)
       (let-values ([(q end-state) (instantiate-var start-state)])
	 body ...)]
      [(_ start-state end-state (q0 q ...) body ...)
       (let-values ([(q0 intermediate-state) (instantiate-var start-state)])
	 (fresh-vars intermediate-state end-state (q ...) body ...))]))

    (define (build-runner state query . conjuncts)
      (make-runner (make-incomplete (conj conjuncts) state) query 'table)))
