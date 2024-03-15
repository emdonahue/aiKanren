;;TODO make tassert capture file and line number
(library (test-runner)
  (export tassert tmessage test-case)
  (import (chezscheme))

  (define failed (make-parameter 0))
  (define total (make-parameter 0))
  (define print-tests? (make-parameter #t))

  (define (tmessage)
    (if (= 0 (failed)) (printf "Pass (~s)~%" (total))
        (printf "Failed: ~s/~s~%" (failed) (total))))

  (define-syntax test-case
    (syntax-rules ()
      [(_ name body ...)
       (let ([fail-count (failed)]
             [total-count (total)])
         (failed 0)
         (total 0)
         (printf "Testing: ~s... " 'name)
         body ...
         (tmessage)
         (failed (+ (failed) fail-count))
         (total (+ (total) total-count)))]))

  (define (noop-handler . x) (apply values x))
  
  (define-syntax tassert
    (syntax-rules ()
      [(_ title received! expected!) (tassert title received! noop-handler expected!)]
      [(_ title received! handler expected!)
       (with-exception-handler
        (lambda (e)
          (printf "Exception in ~s~%" title)
          (unless (eq? noop-handler handler)
                  (printf "Generated: ")
                  (pretty-print (let ([received-values (call-with-values (lambda () received!) list)])
                                  (if (fx= 1 (length received-values)) (car received-values) received-values))))
          (failed (fx1+ (failed)))
          (raise e))
        (lambda ()
          (total (fx1+ (total)))
          (let* ([expected expected!]
                 [received-values (call-with-values (lambda () received!) list)]
                 [received-handled (call-with-values (lambda () (apply handler received-values)) list)]
                 [received (if (fx= 1 (length received-handled)) (car received-handled) received-handled)])
            (when (and (not (equal? expected received)) (or (not (procedure? expected)) (not (expected received))))
              (failed (fx1+ (failed)))
              (parameterize ([pretty-initial-indent 10]
                             [pretty-standard-indent 0])
                (printf "Failed: ~s~%" title)
                (unless (eq? noop-handler handler)
                  (printf "Generated: ")
                  (pretty-print received-values))
                (printf "Expected: ")
                (pretty-print (if (procedure? expected) 'expected! expected))
                (printf "Received: ")
                (pretty-print received)
                (printf "~%"))))))])))
