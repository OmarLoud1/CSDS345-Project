#lang racket

(require "Interpreter.rkt")

(removevar-cps '(d 5) '(a b c d e f) '(1 2 3 4 5 6) (lambda (v1 v2) (list v1 v2)))
(removevar '(d 5) '((a b c d e f) (1 2 3 4 5 6)))


(Minteger '(+ (* 3 2) (- 3 2)) '())
7

(Minteger '(% (/ 6 2) (- 4 2)) '())
1

(Mbool '(&& #t #t) '())
(Mbool '(|| #t #f) '())
(Mbool '(! #t) '())
(Mbool '(== 5 2) '())
(Mbool '(!= 5 2) '())
(Mbool '(< 5 2) '())
(Mbool '(> 5 2) '())
(Mbool '(>= 5 5) '())
(Mbool '(<= 5 5) '())