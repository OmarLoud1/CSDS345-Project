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
    (if (or (null? (cdr list)) (null? (cdr (cdr list))))
        '()
        (car (cdr (cdr list))))))

(define vars
  (lambda (state)
    (car state)))

(define vals
  (lambda (state)
    (car (cdr state))))

(define parameters
  (lambda (expr)
    (cdr expr)))

(provide Minteger)
; Finds the integer value of an expression
(define Minteger
  (lambda (expr state)
    (cond
      ((number? expr) expr)
      ((not (list? expr))       (getState expr state))
      ((eq? (operator expr) '+) (+         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '-) (-         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '*) (*         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '/) (quotient  (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '%) (remainder (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      (else (error 'unknownop "Bad Operator"))))) 

; tests if two expressions are not equal
(define neq?
  (lambda (expr1 expr2)
    (not (eq? expr1 expr2))))

; Finds the boolean value of an expression
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

; checks if a variable is initialized
(define initialized?
  (lambda (var state)
    (member? var (car state))))


(provide getState)
; Gets the value of a variable
(define getState
  (lambda (varName state)
    (cond
      [(or (null? (car state)) (null? (car (cdr state))))                                                        '()]
      [(eq? varName (car (vars state)))                                                           (car (cadr state))]
      [(not (eq? varName (car (car state))))          (getState varName (list (cdr (car state)) (cdr (cadr state))))]
      [else                                        (error 'gStateError "There was a problem finding that variable.")]
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
  (lambda (var val state)
    (if (null? val)
        (StateUpdate (list var '$null$) state)
        (StateUpdate (list var (Minteger val state)) state))))


; assigns a value to a variable
(define M_assign
  (lambda (var val state)
      (StateUpdate (list var (Minteger val state)) state)))


; executes an if expression given a condition, an expression to execute if true, an expression to execute if false, and the state
(define M_if
  (lambda (condition expr exprelse state)
    (cond
      [(eq? (Mbool condition state) #t)     (StateUpdate (M_statement expr state) state)]
      [(eq? (Mbool condition state) #f) (StateUpdate (M_statement exprelse state) state)])))


; executes a while loop given a condition, an expression to execute while true, and the state
(define M_while
  (lambda (condition expr state)
    (cond
      [(Mbool condition state) (M_while condition expr (StateUpdate (M_statement expr state) state))]
      [else state])))

(define M_return
  (lambda (expr state)
    (StateUpdate (list 'return (M_statement expr state)) state)))


; determines the type of statement and executes its function
(define M_statement
  (lambda (expr state)
    (cond
      [(intexp? expr)                                                             (Minteger expr state)]
      [(boolexp? expr)                                                               (Mbool expr state)]
      [(eq? (operator expr) 'return)                                    (M_return (operand expr) state)]
      [(eq? (operator expr) 'var)              (M_declare (leftoperand expr) (rightoperand expr) state)]
      [(eq? (operator expr) '=)                 (M_assign (leftoperand expr) (rightoperand expr) state)]
      [(eq? (operator expr) 'if)     (M_if (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state)]
      [(eq? (operator expr) 'while)              (M_while (leftoperand expr) (rightoperand expr) state)]
      [else (error 'unknownop "Bad Statement")])))


(define intexp?
  (lambda (expr)
    (cond
      ((number? expr) #t)
      ((not (list? expr)) #t)
      ((eq? (operator expr) '+) #t)
      ((eq? (operator expr) '-) #t)
      ((eq? (operator expr) '*) #t)
      ((eq? (operator expr) '/) #t)
      ((eq? (operator expr) '%) #t)
      (else #f))))

; Finds the boolean value of an expression
(define boolexp?
  (lambda (expr)
    (cond
      [(boolean? expr) expr]
      [(eq? (operator expr) '&&) #t]
      [(eq? (operator expr) '||) #t]
      [(eq? (operator expr) '!)  #t]
      [(eq? (operator expr) '==) #t]
      [(eq? (operator expr) '!=) #t]
      [(eq? (operator expr) '<)  #t]
      [(eq? (operator expr) '>)  #t]
      [(eq? (operator expr) '<=) #t]
      [(eq? (operator expr) '>=) #t]

      (else #f))))
    


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
    (list (cons (car declared) (vars state)) (cons (vals declared) (vals state)))))

(provide StateUpdate)
; updates status given a declared variable
(define StateUpdate
  (lambda (declared state)
    (cond
      [(or (null? declared) (null? (car declared))) state]
      [(list? (vars declared)) (StateUpdate (list (car (vars declared)) (car (vals declared))) (StateUpdate (list (cdr (vars declared)) (cdr (vals declared))) state))]
      [else (addState declared (removevar declared state))])))

; iterates across statement list executing expressions
(define M_statementlist
  (lambda (expr state)
    (if (null? (cdr expr))
        (getState 'return (M_statement (car expr) state))
        (M_statementlist (cdr expr) (M_statement (car expr) state)))))

(define run
  (lambda (expr)
    (M_statementlist expr '(() ()))))

(run (parser "tests/test1.txt"))
