#lang racket

; splitting expr
(define operator
  (lambda (list)
    (car list)))

(define operand
  (lambda (list)
    (car (cdr list))))

(define leftoperand
  (lambda list
    (car (cdr list))))

(define rightoperand
  (lambda list
    (car (cdr (cdr list)))))


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

(define Mdefinestate
  (lambda (expr state)
    (cond
      [(eq? (operator expr) 'def) (cons (cons (leftoperand expr) (Minteger (rightoperand expr) state)) state)]
      (else (error 'unknownop "Bad Operator")))))

(define inList
  (lambda (k lis)
    (cond
      [(null? lis) #f]
      [(eq? (car lis) k) #t]
      [(inList var (cdr lis))]

(define initialized?
  (lambda (var state)
    (inList var (car lis))


(define MRemoveState
  (lambda (var state)
    
      
; adds a state to the state table from a declaration expression
(define MAddState
  (lambda (state expr1)
    (cond
    [(null? state) 'NoState]
    [(eq? (car (cdr expr1)) (car (car state)))  (cons (car state)   ]
    [()]
    )))

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

(define replace
  (lambda (y lis)
    (cond
      [(null? lis) '()]
      [(eq? (car lis) x) (cons y (replace x y (cdr lis)))]
      [else (cons (car lis) (replace x y (cdr lis)))])))

(define remove
  (lambda (var lis))
    (cond 
      [(null? lis) '()]
      [(eq? (car lis) var) (cdr lis)]
      [else (cons (car lis) (remove var (cdr lis)))]))

(define member?
  (lambda (x list)
    (cond
      ((null? list) #f)
      ((eq? x (car list)) #t)
      (else member? x (cdr list)))))


(define M_declare
  (lambda (expr state)
    (cons (operand) (cons '$null$ '()))))


(define M_assign
  (lambda (expr state)
      (MAddState leftoperand (Minteger (rightoperand state)) (MRemoveState leftoperand state)))]


(define Mif
  (lambda (expr state)
    (cond
      [(Mbool (car expr) state) (Mif (cdr expr) state)])))


(define Mwhile
  (lambda (expr state)
    (cond
      [(Mbool (car expr) state) (Mwhile (cdr expr) state)]
      (else state))))


(define M_statement
  (lambda (expr state)
    [(eq? (operator expr) 'var)   (M_assign  (operand expr) state]
    [(eq? (operator expr) '=)     (M_assign (operand expr) state]
    [(eq? (operator expr) 'if)    (M_if      (operand expr) state]
    [(eq? (operator expr) 'while) (M_while   (operand expr) state]
    (else (error 'unknownop "Bad Statement"))))) ))

; this isn't right, it need to be fixed so it removes a value
(define removeVar 
  (lambda (var state)
    (cond
      [(null? state) (cons '() '())]
      [(eq? (car (car lis)) var) (cons (cdr (car lis)) (cdr (cdr lis)))))]
      [else (cons (car lis) (removeVar var (cdr lis)))])))
    

; this needs to be fixed because it only works if the variable hasn't been declared yet
(define StateUpdate
  (lambda (declared state)
    (cond
      [(declared? declared state) (cons (cons (car declared) (car state)) (remove (car declared) state))]

(define M_statementlist
  (lambda (expr state)
    (M_statementlist (cdr expr) (StateUpdate (M_statement (car expr) state) state)))
