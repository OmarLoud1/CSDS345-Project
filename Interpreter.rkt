;;;; ***************************************************
;;;; Group 6: Omar Loudghiri(oxl51), Kyler Rosen(kkr33), Niels Sogaard(nks69)
;;;; CSDS 345 Spring 2023
;;;; Project Part 3
;;;; 04/14/2023
;;;; ***************************************************


;Basic Interpreter
#lang racket

(require rackunit)
(require "functionParser.rkt")

;;;; ***************************************************

;Helper functions to parse the lists of expressions

;;;; ***************************************************

; abstraction to create new 
(define newframe
  (lambda ()
    '(()())))

; create a new frame
(define newstate
  (lambda ()
    (list (newframe))))

;gets the operator in an expression
(define operator
  (lambda (list)
    (car list)))

;gets the arguments of an expression
(define args
  (lambda (list)
    (cdr list)))

;finds the next lines of an expression
(define nextLines
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
     ((null? list)                               list)
     ((zero? n)                            (car list))
     (else           (operandn (- n 1) (cdr list))))))

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

;retruns the variables from the state
(define stateVars
  (lambda (state)
    (car (car state))))

;returns the values from the state
(define stateVals
  (lambda (state)
    (car (cdr (car state)))))

; retunrs the varibale from
(define exceptionVar
  (lambda (statement)
    (car (car (cdr statement))))) 

;returns the body of statement 
(define body
  (lambda (statement)
    (caddr statement)))

; add a begin to a block statement, to reuse block code for try accept
(define statementIntoBlock
  (lambda (statement)
    (cond
      [(null? statement) statement]
      [else  (cons 'begin (car (cdr statement)))])))

; adds a begin to a try statement, abstraction
(define tryIntoBlock
  (lambda (try)
    (cons 'begin try)))

;adds a begin to except block, abstraction
(define exceptIntoBlock
  (lambda (except)
    (statementIntoBlock except)))

; adds a begin to to a finally block
(define finallyIntoBlock
  (lambda (finally)
    (statementIntoBlock finally)))

; checks if a variable is initialized
(define initialized?
  (lambda (var state)
    (member? var (car state))))

; #returns a inner version of state
(define deepState
  (lambda (state)
    (cdr state)))


; gets the closure body from state
(define getClosureBody 
  (lambda (state)
    (cadr state)))

; gets the closure function from state
(define getClosure
  (lambda (state) 
    (car state)))

; # returns the outer layer vars from state by calling outerLayer
(define outerLayerVars
  (lambda (state)
    (cadr (outerLayer state))))

; recursively finds the end of state until it gets to the last element
(define outerLayer
  (lambda (state)
    (cond
      [(null? (cdr state))              (car state)]
      [else                (outerLayer (cdr state))])))


; gets the main body from a given expression list
(define mainBody
  (lambda (expr-list)
    (car (cdddar expr-list))))

; # (This isn't used outside of here)
(define modifiers
  (lambda (expr)
    (cdr expr)))

; gets the first expression in a given expression list
(define firstExpr
  (lambda (expr-list)
    (car expr-list)))

; returns the parameters of a function call
(define funcallParams
  (lambda (l)
    (cddr l)))

; gets the arguments for a function call
(define funcargs
  (lambda (list)
    (cdr (cdr list))))


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

; checkss if a variable is inside a list (possibly a list of lists)
(define member?*
  (lambda (a list)
    (cond 
      [(null? list)                                                          #f]
      [(list? (car list))  (or (member?* a (car list)) (member?* a (cdr list)))]
      [(eq? a (car list))                                                    #t]
      [else                                             (member?* a (cdr list))])))

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
      [(null? lis)                                      lis]
      [(eq? (car lis) var)                        (cdr lis)]
      [else (cons (car lis)         (remove var (cdr lis)))])))

;checks if an element is in the list
(define contains?
  (lambda (x list)
    (cond
      [(null? list)               #f]
      [(eq? x (car list))         #t]
      [else (contains? x (cdr list))])))

; checks if a variable is declared
(define declared?
  (lambda (var state)
    (cond
      [(null? state)                                                      #f]
      [else (or (member? var (stateVars state)) (declared? var (cdr state)))])))

; updates the value within the box
(define set-box
  (lambda (box val)
    (begin (set-box! box val) box)))

; adds a frame when begin is called
(define addFrame
  (lambda (state)
      (cons (newframe) state)))

      
;;;; ***************************************************

; Main functions to parse the statements

;;;; ***************************************************

; determines the type of statement and executes its function
(define Mstate
  (lambda (expr state return break continue throw)
    (cond
      [(null? expr)                                                                                                           state]
      [(intexp? expr state)                                                                             (Minteger expr state throw)]
      [(boolexp? expr state)                                                                               (Mbool expr state throw)]
      [(eq? (operator expr) 'function)                                    (MfuncDef expr state return break continue throw)]
      [(eq? (operator expr) 'funcall)                                          (MfuncState expr state return break continue throw)]
      [(eq? (operator expr) 'return)                                     (Mreturn (operand expr) state return break continue throw)]
      [(eq? (operator expr) 'var)                                     (Mdeclare (leftoperand expr) (rightoperand expr) state throw)]
      [(eq? (operator expr) '=)                           (Mupdate (leftoperand expr) (Mval (rightoperand expr) state throw) state)]
      [(eq? (operator expr) 'if)      (Mif (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state return break continue throw)]
      [(eq? (operator expr) 'while)                              (Mwhile (leftoperand expr) (rightoperand expr) state return throw)]
      [(eq? (operator expr) 'break)                                                                            (Mbreak state break)]
      [(eq? (operator expr) 'continue)                                                                   (Mcontinue state continue)]
      [(eq? (operator expr) 'begin)                                          (Mbegin (args expr) state return break continue throw)]
      [(eq? (operator expr) 'try)    (Mtry (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state return break continue throw)]
      [(eq? (operator expr) 'throw)                                                 (throw (Mval (operand expr) state throw) state)]
      [else                                                                                      (error 'unknownop "Bad Statement")])))


; Finds the integer value of an expression
(define Minteger
  (lambda (expr state throw)
    (cond
      [(number? expr)                                                                                               expr]
      [(box? expr)                                                                                          (unbox expr)]
      [(not (list? expr))                                                                         (MgetState expr state)]
      [(and (empty? (rightoperand expr)) (eq? (operator expr) '-))          (- 0  (Mval (leftoperand expr) state throw))]
      [(eq? (operator expr) '+) (+         (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '-) (-         (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '*) (*         (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '/) (quotient  (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '%) (remainder (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [else                                                                            (error 'unknownop "Bad Operator")]))) 



; Finds the boolean value of an expression
(define Mbool
  (lambda (expr state throw)
    (cond
      [(boolean? expr)                                                                                                      expr]
      [(eq? 'true expr)                                                                                                       #t]
      [(eq? 'false expr)                                                                                                      #f]
      [(not (list? expr))                                                                                 (MgetState expr state)]
      [(eq? (operator expr) '&&)              (and (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '||)               (or (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '!)                                                      (not (Mval (leftoperand expr) state throw))]
      [(eq? (operator expr) '==)              (eq? (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '!=)             (neq? (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '<)                 (< (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '>)                 (> (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '<=)               (<= (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [(eq? (operator expr) '>=)               (>= (Mval (leftoperand expr) state throw) (Mval (rightoperand expr) state throw))]
      [else                                                                                    (error 'unknownop "Bad Operator")])))

; Gets the state of the variable from state
(define MgetState
  (lambda (varName state)
    (cond
      [(null? state)                             (error 'gStateError "The variable has not been declared.")]
      [(contains? varName (stateVars state))                          (MgetStateLayer varName (car state))]
      [else                                                                 (MgetState varName (cdr state))])))


; Gets the value of a variable
(define MgetStateLayer
  (lambda (varName layer)
    (cond
      [(or (null? (vals layer)) (null? (vars layer)))                              (error 'gStateError "There was a problem finding that variable.")]
      [(and (eq? varName (car (vars layer))) (eq? '$null$ (car (vals layer))))   (error 'gStateError "This variable has not been assigned a value.")]
      [(eq? varName (car (vars layer)))                                                                                   (unbox (car (vals layer)))]
      [(not (eq? varName (car (vars layer))))                                 (MgetStateLayer varName (list (cdr (vars layer)) (cdr (vals layer))))]
      [else                                                                        (error 'gStateError "There was a problem finding that variable.")])))  


; delares a variable
(define Mdeclare
  (lambda (var val state throw)
    (if (null? val)
        (StateUpdate (list var '$null$) state)
        (StateUpdate (list var (Mval val state throw)) state))))


; assigns a value to a variable
(define Massign
  (lambda (var val state throw)
    (if (declared? var state)
      (StateUpdate (list var (Mval val state throw)) state)
      (error 'gStateError "The variable was not declared."))))


;check either boolean or integer
(define Mval
  (lambda (expr state throw)
    (cond
     [(boolexp? expr state)                                                                       (Mbool expr state throw)]
     [(intexp? expr state)                                                                     (Minteger expr state throw)]
     [(eq? 'funcall (operator expr))                                                           (MfuncVal expr state throw)]
     [(list? expr)                                                                                                    expr]
     [else                            (error 'gStateError (string-append "Variable not declared: " (symbol->string expr)))])))
  


; executes an if expression given a condition, an expression to execute if true, an expression to execute if false, and the state
(define Mif
  (lambda (condition expr exprelse state return break continue throw)
    (cond
      [(eq? (Mbool condition state throw) #t)     (Mstate expr state return break continue throw)]
      [(not(null? exprelse))                  (Mstate exprelse state return break continue throw)]
      [else                                                                                 state])))


; executes a while loop given a condition, an expression to execute while true, and the state
(define Mwhile
  (lambda (condition expr state return throw)
    (call/cc
      (lambda (break)
        (cond
          [(Mbool condition state throw) (Mwhile condition expr (Mstate expr state return break 
                                         (lambda (state2) (break (Mwhile condition expr state2 return throw))) throw) return throw)]
          [else                                                                                                               state])))))

; handles the try block
(define Mtry
  (lambda (try except finally state return break continue throw)
    (call/cc
     (lambda (jump)
         (Mstate (finallyIntoBlock finally)
                          (Mstate (tryIntoBlock try)
                                      state
                                      (lambda (v) (begin (Mstate (finallyIntoBlock finally) state return break continue throw) (return v)))
                                      (lambda (state2) (break (Mstate (finallyIntoBlock finally) state2 return break continue throw)))
                                      (lambda (state2) (continue (Mstate (finallyIntoBlock finally) state2 return break continue throw)))
                                      (exceptContinuation except finally state return break continue throw jump))
                          return break continue throw)))))

; creates the exception continuation for Mtry
(define exceptContinuation
  (lambda (except finally state return break continue throw jump)
    (cond
      [(null? except)
                      (lambda (exception state2) (throw exception (Mstate (finallyIntoBlock finally) state2 return break continue throw)))] 
      [(not (eq? 'catch (operator except)))                                                              (error "Incorrect catch statement")]
      [else
            (lambda (exception state2) (jump (Mstate (finallyIntoBlock finally)
                                    (popFrame (MstateList
                                                 (body except)
                                                 (Mdeclare (exceptionVar except) exception (addFrame state) throw)
                                                 return 
                                                 (lambda (state2) (break (popFrame state2))) 
                                                 (lambda (state2) (continue (popFrame state2))) 
                                                 (lambda (exception2 state2) (throw exception2 (popFrame state2)))))
                                    return break continue throw)))])))


;returns the value of the expression given
(define Mreturn
  (lambda (expr state return break continue throw)
    (cond
      [(eq? (Mval expr state throw) #t)                  (return "true")]
      [(eq? (Mval expr state throw) #f)                 (return "false")]
      [else                             (return (Mval expr state throw))])))


;updates the state instead of deleting and adding again
(define Mupdate
  (lambda (varName val state)
    (cond
      [(null? state)                                              (error 'gStateError "The variable has not been declared.")]
      [(contains? varName (stateVars state))  (cons (begin (Mupdate_layer varName val (car state)) (car state)) (cdr state))]
      [else                                                             (cons (car state) (Mupdate varName val (cdr state)))])))

; Gets the value of a variable
(define Mupdate_layer
  (lambda (varName val layer)
    (cond
      [(or (null? (vals layer)) (null? (vars layer)))                                  (error 'gStateError "There was a problem finding that variable.")]
      [(and (eq? varName (car (vars layer))) (eq? '$null$ (car (vals layer))))       (error 'gStateError "This variable has not been assigned a value.")]
      [(eq? varName (car (vars layer)))                                                                                 (set-box (car (vals layer)) val)]
      [(not (eq? varName (car (vars layer))))                                   (Mupdate_layer varName val (list (cdr (vars layer)) (cdr (vals layer))))]
      [else                                                                            (error 'gStateError "There was a problem finding that variable.")])))  

; helper that calls break
(define Mbreak
  (lambda (state break)
    (break state)))

; helper that calls continue
(define Mcontinue
  (lambda (state continue)
    (continue state)))

; enters the begin statement and defines the break continue and throw 
(define Mbegin
  (lambda (expr-list state return break continue throw)
    (popFrame (MstateList expr-list (addFrame state) return
                                         (lambda (state1) (break (popFrame state1)))
                                         (lambda (state1) (continue (popFrame state1)))
                                         (lambda (exception state1) (throw exception (popFrame state1)))))))


; adds the declared variable to the state, removes past instance of it
(define addState
  (lambda (declared state)
    (cond
      [(and (eq? (vals declared) "true") (neq? (vars declared) 'return))    (list (list (cons (vars declared) (stateVars state))
                                                                                  (cons (box #t) (stateVals state))) (cdr state))]
      [(and (eq? (vals declared) "false") (neq? (vars declared) 'return))   (list (list (cons (vars declared) (stateVars state))
                                                                                  (cons (box #f) (stateVals state))) (cdr state))]
      [else                                                          (cons  (list (cons (vars declared) (stateVars state))
                                                                                  (cons (box (vals declared)) (stateVals state)))
                                                                                                                     (cdr state))])))

; updates status given a declared variable
(define StateUpdate
  (lambda (declared state)
    (cond
      [(or (null? declared) (null? (car declared)))                                                              state]
      [(list? (vars declared))                 (StateUpdate (list (car (vars declared)) (car (vals declared)))
                                               (StateUpdate (list (cdr (vars declared)) (cdr (vals declared))) state))]
      [else                                                             (addState declared (removeVar declared state))])))


; returns the current frame
(define popFrame
  (lambda (state)
    (cond 
      [(null? state)         state]
      [else            (cdr state)])))

 ; cps helper function for remove  
(define removeVar-cps
  (lambda (declared statevars statevals return)
    (cond
      [(null? statevars)                                                            (return statevars statevals)]
      [(eq? (car statevars) (car declared))                             (return (cdr statevars) (cdr statevals))]
      [else (removeVar-cps declared (cdr statevars) (cdr statevals) 
                                  (lambda (v1 v2) (return (cons (car statevars) v1) (cons (car statevals) v2))))])))


; removes the declared variable from the state
(define removeVar
  (lambda (declared state)
    (cons (removeVar-cps declared (stateVars state) (stateVals state) (lambda (v1 v2) (list v1 v2))) (cdr state))))

;checks whether an expression is an integer expression
(define intexp?
  (lambda (expr state)
    (cond
      [(number? expr)                                                    #t]
      [(and (box? expr) (number? (unbox expr)))                          #t]
      [(and (declared? expr state) (number? (MgetState expr state)))     #t]
      [(not (list? expr))                                                #f]
      [(eq? (operator expr) '+)                                          #t]
      [(eq? (operator expr) '-)                                          #t]
      [(eq? (operator expr) '*)                                          #t]
      [(eq? (operator expr) '/)                                          #t]
      [(eq? (operator expr) '%)                                          #t]
      [else                                                              #f])))

; Finds the boolean value of an expression
(define boolexp?
  (lambda (expr state)
    (cond
      [(boolean? expr)                                                   #t]
      [(eq? 'true expr)                                                  #t]
      [(eq? 'false expr)                                                 #t]
      [(and (declared? expr state) (boolean? (MgetState expr state)))    #t]
      [(not (list? expr))                                                #f]
      [(eq? (operator expr) '&&)                                         #t]
      [(eq? (operator expr) '||)                                         #t]
      [(eq? (operator expr) '!)                                          #t]
      [(eq? (operator expr) '==)                                         #t]
      [(eq? (operator expr) '!=)                                         #t]
      [(eq? (operator expr) '<)                                          #t]
      [(eq? (operator expr) '>)                                          #t]
      [(eq? (operator expr) '<=)                                         #t]
      [(eq? (operator expr) '>=)                                         #t]
      [else                                                              #f])))


;handles the main function
(define Mmain
  (lambda (expr-list state return break continue throw)
    (cond
      [(null? expr-list)                                                                      (error "There was a problem handling a function.")]
      [(and (eq? (operator (firstExpr expr-list)) 'function)
       (eq? (leftoperand (firstExpr expr-list)) `main))          (MstateList (mainBody expr-list) (addFrame state) return break continue throw)]
      [else                                                                           (Mmain (args expr-list) state return break continue throw)])))



; This handles expressions that define functions
(define MfuncDef
  (lambda (expr state return break continue throw)
    (Mdeclare (operand expr) (functionClosure expr state) state throw)))
 
; Returns the closure function for a given expression
(define functionClosure
  (lambda (expr state)
    (list (operandn 2 expr) (operandn 3 expr) (lambda (env) (functionState expr (outerLayerVars env) env)))))

; matches the outer variables to the ones within the function
(define functionState
  (lambda (expr outerVars state)
    (cond
      [(null? outerVars)                                                                               (list (outerLayer state))]
      [(or (number? (unbox (getClosure outerVars))) (eq? (length (unbox (getClosure outerVars))) 1)) 
                                                                                 (functionState expr (deepState outerVars) state)]
      [(member?* 'function (getClosureBody (unbox (getClosure outerVars))))                                             state]
      [else                                                                       (functionState expr (deepState outerVars) state)])))

; handles function calls from the parser 
(define MfuncVal  
  (lambda (expr state throw)
    (call/cc
      (lambda (return)
        (MfuncExecute expr state return (lambda (s) ('error "break-out-of-loop")) (lambda (s) ('error "no-continue-statement")) throw)))))

; handles modifying the state for function calls being defined by the parser.\ 
(define MfuncState  
  (lambda (expr state return break continue throw)
    (MfuncExecute expr state (lambda (v) state) (lambda (s) ('error "break-out-of-loop")) (lambda (s) (continue s)) throw)))
    
; this will execute a given function call defined in expr
(define MfuncExecute
  (lambda (expr state return break continue throw)
    (let* ((closure (MgetState (operand expr) state))
           (inner ((body closure) state))
           (middle (addFrame inner))
           (outer
            (assignParams (vars closure)
                               (funcargs expr)
                               middle state throw)))
    (if (not (eq? (length (vars closure)) (length (funcallParams expr))))
        ('error "Error: Wrong Number of Parameters")
        (MstateList (getClosureBody closure) outer return break continue throw)))))

; If there are parameters defined in the params list, a new unction will be declared
(define assignParams
  (lambda (params arguments frame state throw)
    (if (null? params)
        frame
        (assignParams (args params) (args arguments)
                         (Mdeclare (firstExpr params) (Mval (firstExpr arguments) state throw) frame throw)
                         state throw))))
      
; iterates across statement list executing expressions
(define MstateList
  (lambda (expr-list state return break continue throw)
    (if (null? expr-list)
        state
        (MstateList (cdr expr-list) (Mstate (car expr-list) state return break continue throw) 
                                                                     return break continue throw))))

; handles the expression lists for global variables
(define Mexprlist-global
  (lambda (expr-list state return break continue throw init-expr-list)
    (if (null? expr-list)
        (Mmain init-expr-list state return break continue throw)
        (Mexprlist-global (nextLines expr-list)
                          (Mexpr-global (operator expr-list) state return break continue throw init-expr-list)
                          return break continue throw init-expr-list))))

;handles expressions for global variables outside of functions
(define Mexpr-global
  (lambda (expr state return break continue throw init-expr-list)
    (cond
      [(eq? 'function (operator expr))                  (MfuncDef expr state return break continue throw)]
      [(eq? '= (operator expr))                      (Massign (leftoperand expr) (rightoperand expr) state throw)]
      [(eq? 'var (operator expr))                   (Mdeclare (leftoperand expr) (rightoperand expr) state throw)]
      [else                                                          ('error "Unknown Statement outside of Main")])))




;;;; ***************************************************
;;;; ***************************************************

; Main method

;;;; ***************************************************
;;;; ***************************************************

; the main method that runs out interpreter on the parsed code and outputs the result
(provide interpret)
(define interpret
  (lambda (expr)
    (call/cc
      (lambda (return)
        (Mexprlist-global expr (newstate) return
                    (lambda (state) (error 'unknownop "No loop to break out of"))
                    (lambda (state) (error 'unknownop "No loop to continue"))
                    (lambda (exception state)
                      (error 'unknownop (string-append "Uncaught exception thrown: " (format "~a" exception))))
                    expr)))))


    
;;;; ***************************************************
;;;; ***************************************************

; Automated testing

;;;; ***************************************************
;;;; ***************************************************
(displayln "Disclaimer: Test 4 takes a long time, but it will return a value")
(define run-tests
  (lambda (i)
    (cond
        [(zero? i)                                       #t]
        [else      (begin (run-tests (- i 1))
                          (displayln"/////////////////////////////////////////////////////////")
                          (displayln (string-append "Executing Test " (format "~a" i)))
                          (displayln "no output: test passed! if error, it is thrown below:")
                          (displayln" ")
                          (let* ([test-file (format "tests3/test~a.txt" i)]
                                 [expected-output (with-input-from-file (format "tests3/test~a-output.txt" i) read)])
                             (check-equal? (interpret (parser test-file)) expected-output)))])))

(run-tests 20)


; (interpret (parser "tests3/test20.txt"))



