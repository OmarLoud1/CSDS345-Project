#lang racket
(require rackunit)
(require "Interpreter.rkt")


(check-equal? (removevar-cps '(d 5) '(a b c d e f) '(1 2 3 4 5 6) (lambda (v1 v2) (list v1 v2))) '((a b c e f) (1 2 3 5 6)))
(check-equal? (removevar '(d 5) '((a b c d e f) (1 2 3 4 5 6))) '((a b c e f) (1 2 3 5 6)))


(check-equal? (Minteger '(+ (* 3 2) (- 3 2)) '()) 7)

(check-equal? (Minteger '(% (/ 6 2) (- 4 2)) '()) 1)

(check-equal? (Mbool '(&& #t #t) '()) #t)
(check-equal? (Mbool '(|| #t #f) '()) #t)
(check-equal? (Mbool '(! #t) '())     #f)
(check-equal? (Mbool '(== 5 2) '())   #f)
(check-equal? (Mbool '(!= 5 2) '())   #t)
(check-equal? (Mbool '(< 5 2) '())    #f)
(check-equal? (Mbool '(> 5 2) '())    #t)
(check-equal? (Mbool '(>= 5 5) '())   #t)
(check-equal? (Mbool '(<= 5 5) '())   #t)

(check-equal? (getState 'd '((a b c d e f) (1 2 3 4 5 6))) 4)


(check-equal? (StateUpdate '(g 7) '((a b c d e f) (1 2 3 4 5 6))) '((g a b c d e f) (7 1 2 3 4 5 6)))
(check-equal? (StateUpdate '(d 7) '((a b c d e f) (1 2 3 4 5 6))) '((d a b c e f) (7 1 2 3 5 6)))