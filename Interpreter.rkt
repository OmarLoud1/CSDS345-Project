#lang racket
(require "simpleParser.rkt")

(define intrepret
  (lambda (file)
    (M_statement (parser file) '(()()) )
  )
)

; splitting expr
(define operator
  (lambda (list)
    (car list)))

(define operand
  (lambda (list)
    (car (cdr list))))

(define operandn
  (lambda (n list)
    (if (zero? n) 
      (car list)
      (operandn (- n 1) (cdr list)))))

(define leftoperand
  (lambda (list)
    (car (cdr list))))

(define rightoperand
  (lambda (list)
    (car (cdr (cdr list)))))


(provide Minteger)
; Finds the integer value o an expression
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

(define neq?
  (lambda (expr1 expr2)
    (not (eq? expr1 expr2))))

(provide Mbool)
(define Mbool
  (lambda (expr state)
    (cond
      [(boolean? expr) expr]
      [(eq? (operator expr) '&&) (and      (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '||) (or       (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '!)  (not      (Mbool    (leftoperand expr) state))]
      [(eq? (operator expr) '==) (eq?      (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '!=) (neq?     (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '<)  (<        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>)  (>        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '<=) (<=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>=) (>=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]

      (else (error 'unknownop "Bad Operator")))))

; checks if a variable is in a list
(define member?
  (lambda (x list)
    (cond
      ((null? list) #f)
      ((eq? x (car list)) #t)
      (else member? x (cdr list)))))

(define initialized?
  (lambda (var state)
    (member? var (car state))))


; I have no idea what this does
(define getState
  (lambda (state varName)
    (cond
      [(or (null? (car state)) (null? (car (cdr state))))                                                   '()]
      [(eq? (varName) (car (car state)))                                                      (car (cdr state))]
      [(not (eq? (varName) (car (car state))))            (getState (list (cdr (car state)) (cdr (cdr state))))]
      [else                                   (error 'gStateError "There was a problem finding that variable.")]
    )
  )
)  

; replaces a variable with a value in a list
(define replace
  (lambda (x y lis)
    (cond
      [(null? lis) '()]
      [(eq? (car lis) x) (cons y (replace x y (cdr lis)))]
      [else (cons (car lis) (replace x y (cdr lis)))])))

; this is currently not being used?
; removes a variable from a list
(define remove
  (lambda (var lis)
    (cond 
      [(null? lis) '()]
      [(eq? (car lis) var) (cdr lis)]
      [else (cons (car lis) (remove var (cdr lis)))])))


; delares a variable
(define M_declare
  (lambda (expr state)
    (list (operand) '$null$ )))


; assigns a value to a variable
(define M_assign
  (lambda (var val state)
      (list var (Minteger (val)))))


; executes an if expression given a condition, an expression to execute if true, an expression to execute if false, and the state
(define M_if
  (lambda (condition expr exprelse state)
    (cond
      [(eq? (Mbool condition state) #t) (M_statement expr)]
      [(eq? (Mbool condition state) #f) (M_statement exprelse)])))


; executes a while loop given a condition, an expression to execute while true, and the state
(define M_while
  (lambda (condition expr state)
    (cond
      [(Mbool condition state) (M_while condition expr (M_statement(expr state)))]
      [else state])))


; determines the type of statement and executes its function
(define M_statement
  (lambda (expr state)
    (cond
      [(eq? (operator expr) 'return)                                       (Mbool (operand expr) state)]
      [(eq? (operator expr) 'var)                                      (M_declare (operand expr) state)]
      [(eq? (operator expr) '=)                 (M_assign (leftoperand expr) (rightoperand expr) state)]
      [(eq? (operator expr) 'if)     (M_if (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state)]
      [(eq? (operator expr) 'while)              (M_while (leftoperand expr) (rightoperand expr) state)]
      [else (error 'unknownop "Bad Statement")])))


(provide removevar-cps)
 ; cps helper function for remove   
(define removevar-cps
  (lambda (declared statevars statevals return)
    (cond
      [(null? statevars)                                                                        (return '() '())]
      [(eq? (car statevars) (car declared))                             (return (cdr statevars) (cdr statevals))]
      [else (removevar-cps declared (cdr statevars) (cdr statevals) 
                                  (lambda (v1 v2) (return (cons (car statevars) v1) (cons (car statevals) v2))))])))

(provide removevar)
; removes the declared variable from the state
(define removevar
  (lambda (declared state)
    (removevar-cps declared (car state) (cadr state) (lambda (v1 v2) (list v1 v2)))))

; adds the declared variable to the state, removes past instance of it
(define addState
  (lambda (declared state)
    (cons (cons (car declared) (car state)) (cons (cdr declared) (cdr state)))))

; updates status given a declared variable
(define StateUpdate
  (lambda (declared state)
    (addState declared (removevar declared state))))

; iterates across statement list executing expressions
(define M_statementlist
  (lambda (expr state)
    (M_statementlist (cdr expr) (StateUpdate (M_statement (car expr) state) state))))




