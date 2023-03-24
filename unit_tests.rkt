#lang racket
(require rackunit)
(require "Interpreter.rkt")
(require "simpleParser.rkt")




(define (run-tests)
  (for ([i (in-range 1 1)])
    (let* ([test-file (format "tests2/test~a.txt" i)]
           [expected-output (with-input-from-file (format "tests2/test~a-output.txt" i) read)])
      (check-equal? (interpret (parser test-file)) expected-output))))

(run-tests)