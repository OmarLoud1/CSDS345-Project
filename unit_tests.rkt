#lang racket
(require rackunit)
(require "Interpreter.rkt")
(require "simpleParser.rkt")



(define run-tests
  (lambda (i)
    (cond
        [(zero? i)                                       #t]
        [else      (begin (run-tests (- i 1))
                          (displayln (string-append "Executing Test " (format "~a" i)))
                          (let* ([test-file (format "tests2/test~a.txt" i)]
                                 [expected-output (with-input-from-file (format "tests2/test~a-output.txt" i) read)])
                             (check-equal? (interpret (parser test-file)) expected-output)))])))

(run-tests 19)