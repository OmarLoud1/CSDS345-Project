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