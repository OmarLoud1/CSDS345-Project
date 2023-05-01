;;;; ***************************************************
;;;; Group 6: Omar Loudghiri(oxl51), Kyler Rosen(kkr33), Niels Sogaard(nks69)
;;;; CSDS 345 Spring 2023
;;;; Project Part 4
;;;; 04/27/2023
;;;; ***************************************************


;Basic Interpreter
#lang racket

(require rackunit)
(require "classParser.rkt")

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

(define protectedOperator
  (lambda (list)
    (if (list? list)
        (operator list)
        '())))

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

(define getStmtList
  (lambda (list)
    (cadddr list)))

(define getObjExpr
  (lambda (object)
    (cadadr object)))

(define superClass
  (lambda (expr)
    (cond
      ((null?  (car (cddr expr))) '())
      (else (car (cdr (caddr expr)))))))

(define getClass
  (lambda (expr)
    (car expr)))
  

(define populateVars
  (lambda (vars parent state)
    (cond
      ((null? parent) vars)
      (else (cons (append (car vars) (caadr (MgetStateLayer parent state)))
      (cons (append (cadr vars) (getObjExpr (MgetStateLayer parent state))) '()))))))

(define objectVals
  (lambda (class state ctime-type)
    (allInstances (getObjExpr (MgetState class state)) state ctime-type)))

(define allInstances
  (lambda (expr state ctime-type)
    (cond
      ((null? expr) '())
      (else (cons (box (Mval (unbox (operator expr))
                                        state
                                        (lambda (v state1) (error "exception thrown"))
                                        ctime-type))
                  (allInstances (modifiers expr) state ctime-type))))))


(define validOperand
  (lambda (expr)
    (not (null? (cdr (cdr expr))))))

(define className
  (lambda (expr)
    (cadr expr)))


(define getObjVars
  (lambda (expr)
    (caadr expr)))

(define getObjVals
  (lambda (expr)
    (cadr expr)))

(define getLeftDot
  (lambda (expr)
    (cadr expr)))

(define getRightDot
  (lambda (expr)
    (caddr expr)))

(define getDot
  (lambda (expr)
    (cadr expr)))

(define isDot
  (lambda (expr)
    (cond
      ((list? (operand expr)) (caadr expr))
      (else (operand expr)))))

(define makeDotExp
  (lambda (expr)
    (cond
      ((list? expr) expr)
      (else (cons 'dot (cons 'this (cons expr '())))))))

(define dotAssignStmt
  (lambda (expr)
     (caddr expr)))

(define getNextObj 
  (lambda (expr)
     (cadadr expr)))

(define getNextFunc 
  (lambda (expr)
    (car (cadadr expr))))

(define superObj
  (lambda (closure)
    (cons 'new (cons (getClass closure) '()))))


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
      
(define returnNotExist
  (lambda (expr)
    (cond
      ((null? expr) #t)
      ((list? (car expr)) (and (returnNotExist (car expr)) (returnNotExist (cdr expr))))
      ((eq? 'return (car expr)) #f)
      (else (returnNotExist (cdr expr))))))

      
;;;; ***************************************************

; Main functions to parse the statements

;;;; ***************************************************

; determines the type of statement and executes its function
(define Mstate
  (lambda (expr state return break continue throw ctime-type)
    (cond
      [(null? expr)                                                                                                                      state]
      [(intexp? expr state)                                                                                        (Minteger expr state throw)]
      [(boolexp? expr state)                                                                                          (Mbool expr state throw)]
      [(eq? (operator expr) 'function)                                                                  (MfuncDef expr state throw ctime-type)]
      [(eq? (operator expr) 'funcall)                                           (MfuncState expr state return break continue throw ctime-type)]
      [(eq? (operator expr) 'return)                                     (Mreturn (operand expr) state return break continue throw ctime-type)]
      [(eq? (operator expr) 'var)                                     (Mdeclare (leftoperand expr) (rightoperand expr) state throw ctime-type)]
      [(eq? (operator expr) '=)                           (Mupdate (leftoperand expr) (Mval (rightoperand expr) state throw ctime-type) state throw ctime-type)]
      [(eq? (operator expr) 'if)      (Mif (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state return break continue throw ctime-type)]
      [(eq? (operator expr) 'while)                              (Mwhile (leftoperand expr) (rightoperand expr) state return throw ctime-type)]
      [(eq? (operator expr) 'break)                                                                                       (Mbreak state break)] ; does not need to include compile type
      [(eq? (operator expr) 'continue)                                                                              (Mcontinue state continue)] ; does not need to include compile type
      [(eq? (operator expr) 'begin)                                          (Mbegin (args expr) state return break continue throw ctime-type)]
      [(eq? (operator expr) 'try)    (Mtry (operandn 1 expr) (operandn 2 expr) (operandn 3 expr) state return break continue throw ctime-type)]
      [(eq? (operator expr) 'throw)                                                 (throw (Mval (operand expr) state throw ctime-type) state)]
      [else                                                                                      (error 'unknownop "Bad Statement")])))


; Finds the integer value of an expression
(define Minteger
  (lambda (expr state throw ctime-type)
    (cond
      [(number? expr)                                                                                               expr]
      [(box? expr)                                                                                          (unbox expr)]
      [(not (list? expr))                                                                         (MgetState expr state)]
      [(and (empty? (rightoperand expr)) (eq? (operator expr) '-))          (- 0  (Mval (leftoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '+) (+         (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '-) (-         (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '*) (*         (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '/) (quotient  (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '%) (remainder (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [else                                                                            (error 'unknownop "Bad Operator")]))) 



; Finds the boolean value of an expression
(define Mbool
  (lambda (expr state throw ctime-type)
    (cond
      [(boolean? expr)                                                                                                                            expr]
      [(eq? 'true expr)                                                                                                                             #t]
      [(eq? 'false expr)                                                                                                                            #f]
      [(not (list? expr))                                                                                                       (MgetState expr state)]
      [(eq? (operator expr) '&&)              (and (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '||)               (or (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '!)                                                                 (not (Mval (leftoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '==)              (eq? (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '!=)             (neq? (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '<)                 (< (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '>)                 (> (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '<=)               (<= (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [(eq? (operator expr) '>=)               (>= (Mval (leftoperand expr) state throw ctime-type) (Mval (rightoperand expr) state throw ctime-type))]
      [else                                                                                    (error 'unknownop "Bad Operator")])))

; Gets the state of the variable from state
(define MgetState
  (lambda (varName state)
    (cond
      [(null? state)                             (error 'gStateError "The variable has not been declared.")]
      [(contains? varName (stateVars state))                          (MgetStateLayer varName (car state))]
      [else                                                                 (MgetState varName (cdr state))])))

(define MgetStateProtected
  (lambda (varName state)
    (cond
      [(null? state)                                                                               '$null$] ; warning, this is a hella hack
      [(contains? varName (stateVars state))                          (MgetStateLayerProtected varName (car state))]
      [else                                                       (MgetStateProtected varName (cdr state))])))

(define MgetStateLayerProtected
  (lambda (varName layer)
    (cond
      [(or (null? (vals layer)) (null? (vars layer)))                              '$null$]
      [(and (eq? varName (car (vars layer))) (eq? '$null$ (car (vals layer))))   '$null$]
      [(eq? varName (car (vars layer)))                                                                                   (unbox (car (vals layer)))]
      [(not (eq? varName (car (vars layer))))                                 (MgetStateLayerProtected varName (list (cdr (vars layer)) (cdr (vals layer))))]
      [else                                                                        '$null$])))


; Gets the value of a variable
(define MgetStateLayer
  (lambda (varName layer)
    (cond
      [(or (null? (vals layer)) (null? (vars layer)))                              (error 'gStateError "There was a problem finding that variable.")]
      [(and (eq? varName (car (vars layer))) (eq? '$null$ (car (vals layer))))   (error 'gStateError "This variable has not been assigned a value.")]
      [(eq? varName (car (vars layer)))                                                                                   (unbox (car (vals layer)))]
      [(not (eq? varName (car (vars layer))))                                 (MgetStateLayer varName (list (cdr (vars layer)) (cdr (vals layer))))]
      [else                                                                        (error 'gStateError "There was a problem finding that variable.")]))) 

(define find
  (lambda (val state)
    (findVar val state)))

(define findVar
  (lambda (val state)
    (let ((rVal (MgetState val state))) ; warning: i fucked with this
      (cond
        [(eq? val '$null$)   (error 'gStateError "There was a problem finding a var")]
        [else rVal]))))

(define findFunc
  (lambda (val state pastState parent)
    (cond
      [(null? parent)  (findVar val state)]
      [(eq? 'err (returnVarIfValid val state)) (findFunc val (getUpdatedState parent pastState) (retrieveParent (find parent pastState)) pastState)]
      [else (findVar val state)])))

(define findCond
  (lambda (val state parent)
      (cond
        ((eq? 'err (returnVarIfValid val state)) (searchByIndex val state parent))
        (else (findVar val state)))))

(define searchByIndex
  (lambda (val state ctime-type)
  (cond
      ((not (member?* 'this state)) (find val state))
      (else (indexSearch (getIndex val (getObjVars ctime-type) #f)
                               (reverse (getObjVals (find 'this state))) ctime-type)))))

(define getIndex
  (lambda (val list inlist)
    (cond
      ((null? list) 0)
      ((eq? inlist #t) (+ 1 (getIndex val (cdr list) inlist)))
      ((eq? (operator list) val) (+ 0 (getIndex val (cdr list) #t)))
      (else (+ 0 (getIndex val (cdr list) inlist))))))


(define findFuncCond
  (lambda (val state pastState parent)
      (cond
        ((eq? '$null$ (MgetStateProtected val pastState)) (findFunc val state pastState parent))
        (else (findVar val pastState)))))

(define searchState
  (lambda (val state)
    (cond 
    [(null? state)              (error "This var was not defined")]
    [(member? val (vars (firstExpr state)))      (searchFrame val (car state))]
    [else                           (searchState val (cdr state))])))

(define searchFrame
  (lambda (val frame)
    (cond
      [(not (member? val (vars frame)))  (error "Could not find variable in frame.")]
      [else                                            (MgetState val frame)])))

(define indexSearch
  (lambda (var state ctime-type)
    (cond
      [(not (member?* 'this state))                                                                      (findVar var state)]
      [(eq? (hasIndex var (caadr ctime-type)) 0)                                                       (unbox (operator list))]
      [else                                       (indexSearch (- (hasIndex var (caadr ctime-type)) 1) (cdr (getList state)))])))

(define returnVarIfValid
  (lambda (val state)
    (let ((rVal (returnStateIfValid val state)))
      (cond
        [(eq? 'err rVal)                   'err]
        [(eq? '$null$ (unbox rVal))          'err]
        [else                        (unbox rVal)]))))

(define returnStateIfValid
  (lambda (val state)
    (cond
      [(null? state)  'err]
      [(member? val (vars (headFrame state)))     (returnFrameIfValid val (headFrame state))]
      [else                                           (returnStateIfValid val (getElements state))])))

(define returnFrameIfValid
  (lambda (val frame)
    (cond
      [(not (member? val (vars frame)))                 'err]
      [else                                     (MgetStateLayer val frame)])))

(define inList?
  (lambda (val list)
    (cond
      [(null? list)                                        #f]
      [(eq? val (car list))                                #t]
      [else                  (inList? val (getElements list))])))

(define getUpdatedState
  (lambda(parent pastState)
    (cons (retrieveClassFuncs (find parent pastState)) '())))

(define getElements cdr)
(define retrieveParent car)
(define headFrame car)
(define retrieveClassFuncs caddr)

(define hasIndex
  (lambda (val list)
  (cond 
    [(eq? val (car list))                                0]
    [else                  (+ 1 (hasIndex val (cdr list)))])))
  
(define getList
  (lambda (state)
    (reverse (caadr (findVar 'this state)))))


; declares a variable
(define Mdeclare
  (lambda (var val state throw ctime-type)
    (if (null? val)
        (StateUpdate (list var '$null$) state)
        (StateUpdate (list var (Mval val state throw ctime-type)) state))))


; assigns a value to a variable
(define Massign
  (lambda (var val state throw ctime-type)
    (if (declared? var state)
      (StateUpdate (list var (Mval val state throw ctime-type)) state)
      (error 'gStateError "The variable was not declared."))))


;check either boolean or integer
(define Mval
  (lambda (expr state throw ctime-type) 
    (cond
     [(boolexp? expr state)                                   (Mbool expr state throw ctime-type)]
     [(intexp? expr state)                                 (Minteger expr state throw ctime-type)]
     [(and (list? expr) (eq? 'funcall (operator expr)))    (MfuncVal expr state throw ctime-type)]
     [(and (list? expr) (eq? 'new (operator expr)))         (objectClosure expr state ctime-type)]
     [(and (list? expr) (eq? 'dot (operator expr)))    (evalDotExpression expr state throw ctime-type #f)]
     [(list? expr)                                                                           expr]
     [else                                                      (MgetState expr state)])))
  


; executes an if expression given a condition, an expression to execute if true, an expression to execute if false, and the state
(define Mif
  (lambda (condition expr exprelse state return break continue throw ctime-type)
    (cond
      [(eq? (Mbool condition state throw) #t)     (Mstate expr state return break continue throw ctime-type)]
      [(not(null? exprelse))                      (Mstate exprelse state return break continue throw ctime-type)]
      [else                                                                                 state])))


; executes a while loop given a condition, an expression to execute while true, and the state
(define Mwhile
  (lambda (condition expr state return throw ctime-type)
    (call/cc
      (lambda (break)
        (cond
          [(Mbool condition state throw) (Mwhile condition expr (Mstate expr state return break 
                                         (lambda (state2) (break (Mwhile condition expr state2 return throw ctime-type))) throw ctime-type) return throw ctime-type)]
          [else                                                                                                               state])))))

; handles the try block
(define Mtry
  (lambda (try except finally state return break continue throw ctime-type)
    (call/cc
     (lambda (jump)
         (Mstate (finallyIntoBlock finally)
                          (Mstate (tryIntoBlock try)
                                      state
                                      (lambda (v) (begin (Mstate (finallyIntoBlock finally) state return break continue throw ctime-type) (return v)))
                                      (lambda (state2) (break (Mstate (finallyIntoBlock finally) state2 return break continue throw ctime-type)))
                                      (lambda (state2) (continue (Mstate (finallyIntoBlock finally) state2 return break continue throw ctime-type)))
                                      (exceptContinuation except finally state return break continue throw jump ctime-type)
                                      ctime-type)
                          return break continue throw ctime-type)))))

; creates the exception continuation for Mtry
(define exceptContinuation
  (lambda (except finally state return break continue throw jump ctime-type)
    (cond
      [(null? except)
                      (lambda (exception state2) (throw exception (Mstate (finallyIntoBlock finally) state2 return break continue throw ctime-type)))] 
      [(not (eq? 'catch (operator except)))                                                              (error "Incorrect catch statement")]
      [else
            (lambda (exception state2) (jump (Mstate (finallyIntoBlock finally)
                                    (popFrame (MstateList
                                                 (body except)
                                                 (Mdeclare (exceptionVar except) exception (addFrame state) throw ctime-type)
                                                 return 
                                                 (lambda (state2) (break (popFrame state2))) 
                                                 (lambda (state2) (continue (popFrame state2))) 
                                                 (lambda (exception2 state2) (throw exception2 (popFrame state2)))
                                                 ctime-type))
                                    return break continue throw ctime-type)))])))


;returns the value of the expression given
(define Mreturn
  (lambda (expr state return break continue throw ctime-type)
    (cond
      [(eq? (Mval expr state throw ctime-type) #t)                  (return "true")]
      [(eq? (Mval expr state throw ctime-type) #f)                 (return "false")]
      [else                             (return (Mval expr state throw ctime-type))])))


;updates the state instead of deleting and adding again
(define Mupdate
  (lambda (varName val state throw ctime-type)
    (cond
      [(null? state)                                              '$null$] ; (error 'gStateError "The variable has not been declared.")
      [(and (eq? (operator varName) 'dot)
            (not (null? (MupdateInstance (dotAssignStmt varName) val
                                 (cons (cons (getObjVars (findCond (getClass (evalDotExpression varName state throw ctime-type #t)) state ctime-type))
                                             (cons (getObjVals (evalDotExpression varName) state throw ctime-type #t) '()))
                                       '())))))
       state]
      [(contains? varName (stateVars state))  (cons (begin (Mupdate_layer varName val (car state) ctime-type) (car state)) (cdr state))]
      [else                                        (cons (car state) (MupdateStaticProtected varName val (cdr state) throw))])))

(define MupdateInstance
  (lambda (var val state)
    (if (member?* var state)
        (MupdateExistingInstance var val state)
        (error 'gStateError (string-append "That variable does not exist:" (format "~a" var))))))

(define MupdateExistingInstance
  (lambda (var val state)
    (if (member? var (vars (firstExpr state)))
        (cons (begin (Mupdate_layer var val (car state)) (car state)) (cdr state))
        (cons (firstExpr state) (MupdateExistingInstance var val (args state))))))

; exists to change the variable but needs to check whether it is in a local environment or non-static
(define MupdateStaticProtected
  (lambda (var val state ctime-type)
    (cond
      [(and (eq? '$null$ (MupdateCheck var val state)) (not (null? (MupdateReverse var val state ctime-type)))) state]
      [else (MupdateInstance var val state)])))

; Changes the binding of the variable if it exists in the environment
(define MupdateCheck
  (lambda (var val state)
    (if (member?* var state)
        (MupdateExistingInstance var val state)
         (error 'gStateError (string-append "That variable does not exist:" (format "~a" var))))))

(define MupdateReverse
  (lambda (var val state ctime-type)
    (cond
      [(not (member?* 'this state)) (MupdateExistingInstance var val state)]
      [else (unbox (operandn (+ 1 (index? var (instanceVars ctime-type) #f)) (reverse (instanceVals (MgetState 'this state)))))])))

(define instanceVars caadr)
(define instanceVals cadr)

(define index?
  (lambda (var l seen?)
    (cond
      [(null? l) 0]
      [(eq? seen? #t) (+ 1 (index? var (cdr l) seen?))]
      [(eq? var (operator l)) (index? var (cdr l) #t)]
      [else (index? var (cdr l) seen?)])))

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
  (lambda (expr-list state return break continue throw ctime-type)
    (popFrame (MstateList expr-list (addFrame state) return
                                         (lambda (state1) (break (popFrame state1)))
                                         (lambda (state1) (continue (popFrame state1)))
                                         (lambda (exception state1) (throw exception (popFrame state1)))
                                         ctime-type))))


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
(define findMain
  (lambda (expr-list state return break continue throw class)
    (cond
      [(null? expr-list)                            (error "There was a problem handling a function.")]
      [(eq? (get-class expr-list) class)  (Mmain (getStmtList (firstExpr expr-list)) state return break continue throw class)]
      [else                           (findMain (args expr-list) state return break continue throw class)])))

(define Mmain
  (lambda (expr-list state return break continue throw class)
  (cond
    [(eq? (leftoperand (firstExpr expr-list)) `main)  (MstateList (mainBody expr-list) (addFrame state) return break continue throw (MgetState class state))]
    [else                                                                                   (Mmain (args expr-list) state return break continue throw class)])))

(define get-class
  (lambda (expr-list)
    (cadar expr-list)))

; This handles expressions that define functions
(define MfuncDef
  (lambda (expr state throw ctime-type)
    (Mdeclare (operand expr) (functionClosure expr state (retrieveContainClass ctime-type)) state throw)))

; Will get and return the class that a given function is contained in
(define retrieveContainClass
  (lambda (closure) 
    (unboxedFromStmtList (caar (getStmtList closure)))))

; retrieves an unboxed value from the statement list
(define unboxedFromStmtList (lambda (stmt-list) (getStmtList (unbox stmt-list))))
 
; Returns the closure function for a given expression
(define functionClosure
  (lambda (expr state class)
    (list (cons 'this (operandn 2 expr)) (operandn 3 expr) (lambda (env) (functionState expr (outerLayerVars env) env)) class)))

(define Mclass
  (lambda (expr state throw)
    (StateUpdate (list (operand expr) (classClosure expr state throw)) state)))

(define classClosure
  (lambda (expr state throw)
    (list (superClass expr)
     (populateVars (getClosure (evalDefinitionList (getStmtList expr) (newstate))) (superClass expr) state)
     (getClosure (evalMethodList (getStmtList expr) (newstate) (className expr) throw)))))


(define evalDefinitionList
  (lambda (exprs state)
   (if (null? exprs)
      state
      (evalDefinitionList (modifiers exprs) (evalDefinition (operator exprs) state)))))

(define evalDefinition
  (lambda (expr state)
    (cond
      ((eq? 'var (operator expr)) (declareDefinitions expr state))
      (else state))))
  
(define declareDefinitions
  (lambda (expr state)
      (cond
        ((validOperand expr) (StateUpdate (list (operand expr) (rightoperand expr)) state))
        (else (Mdeclare (operand expr) '$null$ state)))))


(define evalMethodList
 (lambda (stmts state class throw)
   (if (null? stmts)
      state
      (evalMethodList (modifiers stmts) (evalMethod (operator stmts) state class throw) class throw))))

(define evalMethod
  (lambda (expr state class throw)
    (cond
      ((or (eq? 'function (operator expr)) (eq? 'static-function (operator expr))) (declareFunction expr state class))
      (else state))))

(define declareFunction
  (lambda (expr state class)
    (StateUpdate (list (operand expr)
            (functionClosure expr state class))
            state)))

(define evalDotExpression
  (lambda (expr state throw ctime-type function)
    (evalRightDot (getRightDot expr)
    (evalLeftDot (getLeftDot expr) state throw ctime-type)
                         state throw ctime-type function)))

(define evalLeftDot
  (lambda (object state throw ctime-type)
     (cond
      ((eq? object 'this)  (MgetState 'this state))
      ((eq? object 'super) (objectClosure (superObj ctime-type) state ctime-type))
      ((and (list? object) (eq? (operator object) 'funcall))
       (MfuncVal object state throw ctime-type)) 
      ((list? object)      (objectClosure object state ctime-type))
      (else                (findCond object state ctime-type)))))

(define evalRightDot
  (lambda (expr object state throw ctime-type function)
     (cond
      ((eq? function #t) object)
      (else (Mval expr (cons (cons (getObjVars (MgetState (getClass object) state))
                       (cons (getObjVals object) '())) '()) throw ctime-type)))))

(define findThis
  (lambda (object state throw ctime-type)
     (cond
      ((eq? object 'this)  (MgetState 'this state))
      ((eq? object 'super) (MgetState 'this state))
      ((and (list? object) (eq? (operator object) 'funcall))
       (MfuncVal object state throw ctime-type)) 
      ((list? object)      (objectClosure object state ctime-type))
      (else                (findCond object state ctime-type)))))

(define objectClosure 
  (lambda (expr state ctime-type)
    (list (className expr) (objectVals (className expr) state ctime-type))))

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
  (lambda (expr state throw ctime-type)
    (call/cc
      (lambda (return)
        (MfuncExecute expr state return (lambda (s) ('error "no-continue-statement")) throw ctime-type)))))

; handles modifying the state for function calls being defined by the parser.
(define MfuncState  
  (lambda (expr state return break continue throw ctime-type)
    (MfuncExecute expr state (lambda (v) state) (lambda (s) (continue s)) throw ctime-type)))

(define MfuncExecute
  (lambda (expr state return continue throw ctime-type)
    (let* ((dotExpr (makeDotExp (getDot expr)))
           (compileType (MgetState (getClass (evalDotExpression dotExpr state throw ctime-type #t)) state))    
           (closure (findFuncCond (body dotExpr) (cons (body compileType) '()) state (firstExpr ctime-type)))
           (inner ((body closure) state))
           (middle (addFrame inner))
           (outer (assignParams (vars closure) (cons (findThis (getLeftDot dotExpr) state throw ctime-type) (funcargs expr)) middle state throw ctime-type))    
           (modCompileType (MgetState (getStmtList closure) state)))
           
    
     (cond
      ((not (eq? (- (length (vars closure)) 1) (length (funcallParams expr))))  ('error "Error: Wrong Number of Parameters"))
      ((and (eq? (returnNotExist (getClosureBody closure)) #t) (not (null? (MstateList (getClosureBody closure) outer
                                (lambda (v) state)
                                (lambda (v) ('error "break-out-of-loop"))
                                (lambda (v) (continue v))
                                throw ctime-type)))) state)       
      (else (MstateList (getClosureBody closure) outer return 
                                            (lambda (v) (error "break"))
                                            (lambda (v) (error "there was no return statement")) 
                                            throw modCompileType))))))

; If there are parameters defined in the params list, a new function will be declared
(define assignParams
  (lambda (params arguments frame state throw ctime-type)
    (cond
      [(null? params)   frame]
      [(eq? (vars params) 'this)    (assignParams (args params) (args arguments)
                                                 (StateUpdate (list (firstExpr params) (firstExpr arguments)) frame)
                                                 state throw ctime-type)]
        [else                      (assignParams (args params) (args arguments)
                                                 (StateUpdate (list (firstExpr params) (Mval (firstExpr arguments) state throw ctime-type)) frame)
                                                 state throw ctime-type)])))
      
; iterates across statement list executing expressions
(define MstateList
  (lambda (expr-list state return break continue throw ctime-type)
    (if (null? expr-list)
        state
        (MstateList (cdr expr-list) (Mstate (car expr-list) state return break continue throw ctime-type) 
                                                                     return break continue throw ctime-type))))

; handles the expression lists for global variables
(define Mexprlist-global
  (lambda (expr-list state return break continue throw init-expr-list class)
    (if (null? expr-list)
        (findMain init-expr-list state return break continue throw class)
        (Mexprlist-global (nextLines expr-list)
                          (Mexpr-global (operator expr-list) state return break continue throw init-expr-list class)
                          return break continue throw init-expr-list class))))

;handles expressions for global variables outside of functions
(define Mexpr-global
  (lambda (expr state return break continue throw init-expr-list class)
    (cond
      [(eq? 'class (operator expr))                    (Mclass expr state throw)]
      [else                        ('error "Unknown Statement outside of Main")])))




;;;; ***************************************************
;;;; ***************************************************

; Main method

;;;; ***************************************************
;;;; ***************************************************

; the main method that runs out interpreter on the parsed code and outputs the result
(provide interpret)
(define interpret
  (lambda (file class)
    (call/cc
      (lambda (return)
        (Mexprlist-global (parser file) (newstate) return
                    (lambda (state) (error 'unknownop "No loop to break out of"))
                    (lambda (state) (error 'unknownop "No loop to continue"))
                    (lambda (exception state)
                      (error 'unknownop (string-append "Uncaught exception thrown: " (format "~a" exception))))
                    (parser file) class)))))


    
;;;; ***************************************************
;;;; ***************************************************

; Automated testing

;;;; ***************************************************
;;;; ***************************************************
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

; (run-tests 20)


(interpret "tests4/test4.txt" 'A)



