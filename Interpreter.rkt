#lang racket

(define Minteger
  (lambda (expr state)
    (cond
      ((number? expr) expr)
      ((eq? (operator expr) '+) (+         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '-) (-         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '*) (*         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '/) (quotient  (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '%) (remainder (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      (else (error 'unknownop "Bad Operator")))))

(define !=
  (lambda (expr)
    (not (expr))))

(define Mbool
  (lambda (expr state)
    (cond
      [(boolean? expr) expr]
      [(eq? (operator expr) '&&) (and      (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '||) (or       (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '!)  (not      (Mbool    (leftoperand expr) state))]
      [(eq? (operator expr) '==) (eq?      (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '!=) (         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '<)  (<        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>)  (>        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>=) (<=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>=) (>=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]

      (else (error 'unknownop "Bad Operator")))))

(define operator
  (lambda (list)
    (car list)))

(define leftoperand
  (lambda list
    (car (cdr list))))

(define rightoperand
  (lambda list
    (car (cdr (cdr list)))))