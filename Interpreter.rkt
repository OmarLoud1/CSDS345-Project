;;;; ***************************************************
;;;; Group 6: Omar Loudghiri(oxl51), Kyler Rosen(kkr33), Niels Sogaard(nks69)
;;;; CSDS 345 Spring 2023
;;;; Project 1
;;;; ***************************************************


;Basic Interpreter
#lang racket

(require "simpleParser.rkt")
;;;; ***************************************************
;Helper functions to parse the lists of expressions
;;;; ***************************************************


(define newframe
  (lambda ()
    '(()())))
(define newstate
  (lambda ()
    (list (newframe))))

;gets the operator in an expression
(define operator
  (lambda (list)
    (car list)))

(define args
  (lambda (list)
    (cdr list)))

;gets the operand in an expression
(define operand
  (lambda (list)
    (car (cdr list))))

;gets the nth operand in a multi-operand expression
(define operandn
  (lambda (n list)
    (cond
     ((null? list)                  list)
     ((zero? n)               (car list))
     (else (operandn (- n 1) (cdr list))))))

;gets the left operand in prefix notation
(define leftoperand
  (lambda (list)
    (car (cdr list))))

;gets the right operand
(define rightoperand
  (lambda (list)
    (if (or (null? (cdr list)) (null? (cdr (cdr list))))
        '()
        (car (cdr (cdr list))))))

;gets the parameters of an expression
(define parameters
  (lambda (expr)
    (cdr expr)))

;gets the variable name from the state list
(define vars
  (lambda (state)
    (car state)))

;gets the value of the variable from the list
(define vals
  (lambda (state)
    (car (cdr state))))


;;;; ***************************************************
; Auxiliary helper methods from class
;;;; ***************************************************

; tests if two expressions are not equal
(define neq?
  (lambda (expr1 expr2)
    (not (eq? expr1 expr2))))

; checks if a variable is in a list
(define member?
  (lambda (x list)
    (cond
      ((null? list)             #f)
      ((eq? x (car list))       #t)
      (else (member? x (cdr list))))))

; replaces a variable with a value in a list
(define replace
  (lambda (x y lis)
    (cond
      [(null? lis)                                       lis]
      [(eq? (car lis) x)    (cons y (replace x y (cdr lis)))]
      [else (cons (car lis)         (replace x y (cdr lis)))])))

; this is currently not being used?
; removes a variable from a list
(define remove
  (lambda (var lis)
    (cond 
      [(null? lis)                              lis]
      [(eq? (car lis) var)                (cdr lis)]
      [else (cons (car lis) (remove var (cdr lis)))])))

; checks if a variable is declared
(define declared?
  (lambda (var state)
    (member? var (vars state))))



;;;; ***************************************************
; Main functions to parse the statements
;;;; ***************************************************

; Finds the integer value of an expression
(define Minteger
  (lambda (expr state)
    (cond
      ((number? expr)                                                                                           expr)
      ((not (list? expr))                                                                     (MgetState expr state))
      ((and (empty? (rightoperand expr)) (eq? (operator expr) '-))        (- 0  (Minteger (leftoperand expr) state)))
      ((eq? (operator expr) '+) (+         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '-) (-         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '*) (*         (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '/) (quotient  (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      ((eq? (operator expr) '%) (remainder (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state)))
      (else (error 'unknownop "Bad Operator"))))) 



; Finds the boolean value of an expression
(define Mbool
  (lambda (expr state)
    (cond
      [(boolean? expr)                            expr]
      [(eq? 'true expr)                             #t]
      [(eq? 'false expr)                            #f]
      ((not (list? expr))       (MgetState expr state))
      [(eq? (operator expr) '&&) (and      (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '||) (or       (Mbool    (leftoperand expr) state) (Mbool    (rightoperand expr) state))]
      [(eq? (operator expr) '!)  (not                                          (Mbool     (leftoperand expr) state))]
      [(eq? (operator expr) '==) (eq?      (Mval (leftoperand expr) state)         (Mval (rightoperand expr) state))]
      [(eq? (operator expr) '!=) (neq?     (Mval (leftoperand expr) state)         (Mval (rightoperand expr) state))]
      [(eq? (operator expr) '<)  (<        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>)  (>        (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '<=) (<=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]
      [(eq? (operator expr) '>=) (>=       (Minteger (leftoperand expr) state) (Minteger (rightoperand expr) state))]


      (else (error 'unknownop "Bad Operator")))))


; Gets the value of a variable
(define MgetState
  (lambda (varName state)
    (cond
      [(or (null? (vals state)) (null? (vars state)))                              (error 'gStateError "There was a problem finding that variable.")]
      [(and (eq? varName (car (vars state))) (eq? '$null$ (car (vals state))))   (error 'gStateError "This variable has not been assigned a value.")]
      [(eq? varName (car (vars state)))                                                                                           (car (vals state))]
      [(not (eq? varName (car (vars state))))                                       (MgetState varName (list (cdr (vars state)) (cdr (vals state))))]
      [else                                                                        (error 'gStateError "There was a problem finding that variable.")])))  


; delares a variable
(define Mdeclare
  (lambda (var val state)
    (if (null? val)
        (StateUpdate (list var '$null$) state)
        (StateUpdate (list var (Mval val state)) state))))


; assigns a value to a variable
(define Massign
  (lambda (var val state)
    (if (declared? var state)
      (StateUpdate (list var (Mval val state)) state)
      (error 'gStateError "The variable was not declared."))))


;check either boolean or integer
(define Mval
  (lambda (expr state)
    (cond
     [(boolexp? expr state)                   (Mbool expr state)]
     [(intexp? expr state)                 (Minteger expr state)]
     [else                  (error 'gStateError "Value Unknown")])))
  


; executes an if expression given a condition, an expression to execute if true, an expression to execute if false, and the state
(define Mif
  (lambda (condition expr exprelse state return break continue throw)
    (cond
      [(eq? (Mbool condition state) #t)     (StateUpdate (Mstate expr state return break continue throw) state)]
      [(not(null? exprelse))            (StateUpdate (MstateList exprelse state return break continue throw) state)]
      [else                                                                       state])))


; executes a while loop given a condition, an expression to execute while true, and the state
(define Mwhile
  (lambda (condition expr state return throw)
    (call/cc
      (lambda(break)
        (cond
          [(Mbool condition state) (Mwhile condition expr (Mstate expr state return break 
                                                          (lambda (env) (break (Mwhile condition state env return throw))) throw) return throw)]
          [else                                                                                                           state])))))


(define Mtry
  (lambda (try except finally environment return break continue throw)
    (call/cc
     (lambda (jump)
         (MstateList (finally-into-block finally)
                          (MstateList (try-into-block try)
                                      state
                                      (lambda (v) (begin (Mstatelist (finally-into-block finally) state return break continue throw) (return v)))
                                      (lambda (env) (break (MstateList (finally-into-block finally) env return break continue throw compile-type)))
                                      (lambda (env) (continue (MstateList finally-block env return break continue throw compile-type)))
                                      (except-continuation except state return break continue throw jump (finally-into-block finally))))
                          return break continue throw))))

(define except-continuation
  (lambda (except environment return break continue throw jump finally-block)
    (cond
      ((null? catch-statement)
             (lambda (ex env) (throw ex (Mstatelist finally-block env return break continue throw)))) 
      ((not (eq? 'catch (operator catch-statement)))
             (myerror "Incorrect catch statement"))
      (else
             (lambda (ex env) (jump (Mblock finally-block
                                     (pop-frame (Mstatelist
                                                 (body except)
                                                 (MaddState (catch-var catch-statement) ex (push-frame environment))
                                                 return 
                                                 (lambda (env2) (break (pop-frame env2))) 
                                                 (lambda (env2) (continue (pop-frame env2))) 
                                                 (lambda (v env2) (throw v (pop-frame env2)))))
                                     return break continue throw)))))))

(define body
  (lambda (statement)
    (caddr statement)))

(define statement-into-block
  (lambda (statement)
    (cons 'begin statement)))

(define try-into-block
  (lambda (try)
    (statement-into-block try)))

(define except-into-block
  (lambda (except)
    (statement-into-block except)))

(define finally-into-block
  (lambda (finally)
    (statement-into-block finally)))

(define Mbreak
  (lambda (state break)
    (break state)))

(define Mcontinue
  (lambda (state continue)
    (continue state)))

;returns the value of the expression given
(define Mreturn
  (lambda (expr state return break continue throw)
    (cond
      [(eq? (Mstate expr state return break continue throw) #t)               (return "true")]
      [(eq? (Mstate expr state return break continue throw) #f)              (return "false")]
      [else                          (return (Mstate expr state return break continue throw))])))


; determines the type of statement and executes its function
(define Mstate
  (lambda (expr state return break continue throw)
    (cond
      [(intexp? expr state)                                                                                  (Minteger expr state)]
      [(boolexp? expr state)                                                                                    (Mbool expr state)]
      [(eq? (operator expr) 'return)                                    (Mreturn (operand expr) state return break continue throw)]
      [(eq? (operator expr) 'var)                                          (Mdeclare (leftoperand expr) (rightoperand expr) state)]
      [(eq? (operator expr) '=)                                             (Massign (leftoperand expr) (rightoperand expr) state)]
      [(eq? (operator expr) 'if)     (Mif (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state return break continue throw)]
      [(eq? (operator expr) 'while)                             (Mwhile (leftoperand expr) (rightoperand expr) state return throw)]
      [(eq? (operator expr) 'break)                                                                           (Mbreak state break)]
      [(eq? (operator expr) 'continue)                                                                  (Mcontinue state continue)]
      [(eq? (operator expr) 'begin)                                     (MstateList (args expr) state return break continue throw)]
      [else                                                                                     (error 'unknownop "Bad Statement")])))

; iterates across statement list executing expressions
(define MstateList
  (lambda (expr-list state return break continue throw)
    (if (null? expr-list)
        state
        (MstateList (cdr expr-list) (Mstate (car expr-list) state return break continue throw) 
                                                                     return break continue throw))))


; checks if a variable is initialized
(define initialized?
  (lambda (var state)
    (member? var (car state))))


; adds the declared variable to the state, removes past instance of it
(define addState
  (lambda (declared state)
    (cond
      [(and (eq? (vals declared) "true") (neq? (vars declared) 'return))    (list (cons (vars declared) (vars state))
                                                                                  (cons #t (vals state)))]
      [(and (eq? (vals declared) "false") (neq? (vars declared) 'return))   (list (cons (vars declared) (vars state))
                                                                                  (cons #f (vals state)))]
      [else                                                    (list (cons (vars declared) (vars state))
                                                                     (cons (vals declared) (vals state)))])))


; updates status given a declared variable
(define StateUpdate
  (lambda (declared state)
    (cond
      [(or (null? declared)       (null? (car declared))) state]
      [(list? (vars declared))    (StateUpdate (list (car (vars declared)) (car (vals declared)))
                                               (StateUpdate (list (cdr (vars declared)) (cdr (vals declared))) state))]
      [else                       (addState declared (removevar declared state))])))

(define addFrame
  (lambda (state)
    (cond
      [(null? state) (list (newframe))]
      [else          (cons (newframe) state)]
    )
  )
)

(define popFrame
  (lambda (state)
    (cdr state)
  )
)


 ; cps helper function for remove  
(define removevar-cps
  (lambda (declared statevars statevals return)
    (cond
      [(null? statevars)                                                            (return statevars statevals)]
      [(eq? (car statevars) (car declared))                             (return (cdr statevars) (cdr statevals))]
      [else (removevar-cps declared (cdr statevars) (cdr statevals) 
                                  (lambda (v1 v2) (return (cons (car statevars) v1) (cons (car statevals) v2))))])))


; removes the declared variable from the state
(define removevar
  (lambda (declared state)
    (removevar-cps declared (car state) (cadr state) (lambda (v1 v2) (list v1 v2)))))

;checks whether an expression is an integer expression
(define intexp?
  (lambda (expr state)
    (cond
      ((number? expr)           #t)
      ((and (box? expr) (number? (unbox expr))) #t)
      ((and (declared? expr state) (number? (MgetState expr state))) #t)
      [(not (list? expr))       #f]
      ((eq? (operator expr) '+) #t)
      ((eq? (operator expr) '-) #t)
      ((eq? (operator expr) '*) #t)
      ((eq? (operator expr) '/) #t)
      ((eq? (operator expr) '%) #t)
      (else #f))))

; Finds the boolean value of an expression
(define boolexp?
  (lambda (expr state)
    (cond
      [(boolean? expr)           #t]
      [(eq? 'true expr)          #t]
      [(eq? 'false expr)         #t]
      [(and (declared? expr state) (boolean? (MgetState expr state))) #t]
      [(not (list? expr))        #f]
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

;;;; ***************************************************

;;;; *̵͖̻͋̓͑͜*̸̫͔̽̾͐͜*̴̡̦͋͝͠*̵̢̼͛͊̕͜*̵̡̺͇̐̐͘*̵͓̫̦͋͝͝*̸͇̦͓̓͑̚*̴̦̪͓͘͘̕*̵͔͉͉͑́͝*̸͉̫̻͆͑͝*̵͔͚̐̀̈́*̸̦͓͇̽͊*̴͓̪͚̚̚͠*̸̙̻̘̾͐*̸̡̠̒͜͝͠*̵̟̘̼̾́̓*̵͕͍͎͆̚*̸͎̠̾̾͐*̸̠͓͔̈́̿͝*̵͖͍͉͝͝͝*̸̦͖̟̒͆͒*̵͎͙̫͋̔̓*̵̻͔̾̈́͜͠*̸̡͖̦͛̾͝*̸͕̦̠͐̿̈́*̸͎̙̓̕*̵͉̪̓̈́̕*̸̫̪̘̾͋*̸̠̦́͠*̴̡̞͉͋̀̕*̵̢̪̺́͐*̸͙͚̺̕͘͠*̵̻͕͍͆̔̕*̴̞̠͚̔̚*̴̦͙̠͐͋̀*̴͕͉̫̒̈́̿*̴̙̞̺͆͋̾*̵͕̝̒͋*̵̡͙͋͐̚*̵̞̞̻͑̽͒*̴̦͓͌͐͊*̸̺̪̈́̓͘*̵͚͚̙͆͌͒*̴̢͔͉͐͐͝*̸͇̙͊̀͘͜*̸̠͙͌͝͝*̸͎̦̈́̔͋*̵͇͍̻̓̈́͛*̴̟̪͐͜͠͝*̵̢͍̓͐̓͜*̵̞̪̿͛͑

; Main method

;;;; *̵͖̻͋̓͑͜*̸̫͔̽̾͐͜*̴̡̦͋͝͠*̵̢̼͛͊̕͜*̵̡̺͇̐̐͘*̵͓̫̦͋͝͝*̸͇̦͓̓͑̚*̴̦̪͓͘͘̕*̵͔͉͉͑́͝*̸͉̫̻͆͑͝*̵͔͚̐̀̈́*̸̦͓͇̽͊*̴͓̪͚̚̚͠*̸̙̻̘̾͐*̸̡̠̒͜͝͠*̵̟̘̼̾́̓*̵͕͍͎͆̚*̸͎̠̾̾͐*̸̠͓͔̈́̿͝*̵͖͍͉͝͝͝*̸̦͖̟̒͆͒*̵͎͙̫͋̔̓*̵̻͔̾̈́͜͠*̸̡͖̦͛̾͝*̸͕̦̠͐̿̈́*̸͎̙̓̕*̵͉̪̓̈́̕*̸̫̪̘̾͋*̸̠̦́͠*̴̡̞͉͋̀̕*̵̢̪̺́͐*̸͙͚̺̕͘͠*̵̻͕͍͆̔̕*̴̞̠͚̔̚*̴̦͙̠͐͋̀*̴͕͉̫̒̈́̿*̴̙̞̺͆͋̾*̵͕̝̒͋*̵̡͙͋͐̚*̵̞̞̻͑̽͒*̴̦͓͌͐͊*̸̺̪̈́̓͘*̵͚͚̙͆͌͒*̴̢͔͉͐͐͝*̸͇̙͊̀͘͜*̸̠͙͌͝͝*̸͎̦̈́̔͋*̵͇͍̻̓̈́͛*̴̟̪͐͜͠͝*̵̢͍̓͐̓͜*̵̞̪̿͛͑



(define interpret
  (lambda (expr)
    (call/cc
      (lambda (return)
        (MstateList expr (newstate) return
                    (lambda (state) (error 'unknownop "No loop to break out of"))
                    (lambda (state) (error 'unknownop "No loop to continue"))
                    (lambda (state) (error 'unknownop "Uncaught exception thrown")))))))
    

(interpret (parser "tests/test1.txt"))




