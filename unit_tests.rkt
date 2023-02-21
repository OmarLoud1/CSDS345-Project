#lang racket

(require "Interpreter.rkt")

(removevar-cps '(d 5) '(a b c d e f) '(1 2 3 4 5 6) (lambda (v1 v2) (list v1 v2)))

(removevar '(d 5) '((a b c d e f) (1 2 3 4 5 6)))