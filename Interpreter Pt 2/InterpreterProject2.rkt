#lang racket
(require "simpleParser.rkt")

; Simple Language Interpreter Project Part 2
; Carter Chen
; Victor Majestic
; Matthew Vatne

; NOTE: We were unable to implement try/catch.
; There are likely errors with nested ifs/whiles.
; Break/continue should work as anticipated.

; interpret calls our interpreter with the initial state
; the state consists of a list of pairs, and it is ordered as '((value1 var1) (value2 var2) ...)
(define interpret
  (lambda (filename)
    (interpreter (parser filename) init (lambda (v) v) (lambda (v) v) (lambda (v) v) (lambda (v) v) outBreak)))

(define init '())
(define outBreak #f)
(define inBreak #t)
(define firstTerm caar)
(define rightSubtree cdr)
(define leftSubtree car)
(define returnExpr cdar)
(define stripBegin cdar)

; the interpreter function looks at the first term in the left subtree, or the car of the current list
;   and calls interpreter on the right subtree (the cdr) and the appropriate M_State
;   on the left subtree which is used as the state for the recursive call
(define interpreter
  (lambda (lis state continue return break throw flag)
    (cond
      ((null? lis) state)
      ((equal? (firstTerm lis) 'begin)  (interpreter    (rightSubtree lis) (removeLayer (interpreter (stripBegin lis) (cons '() state) continue return break throw inBreak)) continue return break throw flag))
      ((equal? (firstTerm lis) 'var)    (interpreter    (rightSubtree lis) (M_State_Declaration (leftSubtree lis) state flag) continue return break throw flag))
      ((equal? (firstTerm lis) '=)      (interpreter    (rightSubtree lis) (M_State_Assignment (leftSubtree lis) state) continue return break throw flag))
      ((equal? (firstTerm lis) 'return) (M_State_Return (returnExpr lis) state))
      ((equal? (firstTerm lis) 'continue) (continue state))
      ((equal? (firstTerm lis) 'break) (break state))
      ((equal? (firstTerm lis) 'if)     (interpreter    (rightSubtree lis) (M_State_If (leftSubtree lis) state continue return break throw flag) continue return break throw flag))
      ((equal? (firstTerm lis) 'while) (interpreter (rightSubtree lis) (call/cc (lambda (k) (M_State_While (leftSubtree lis) state continue return k throw flag))) continue return break throw flag))
      (else (error 'UnknownTerm "Unknown Term in Syntax Tree")))))
     

(define removeLayer cdr)

; M_State for begin, equivalently the curly brackets { }
(define M_State_Begin
  (lambda (lis state continue return break throw)
    (interpreter lis state continue return break throw)))
      

(define assignStatement cddr)
(define variable cadr)

; M_State for variable declaration
; First, we check if the variable has already been declared; if this is the case we return an error.
; Otherwise, we check if a value is assigned.
; If a value is assigned, we call declareAndAssign on the var and assignment value using the state
; Otherwise, we call declare on the var using the state.
(define M_State_Declaration
  (lambda (lis state flag)
    (cond
      ((eq? (varLookupLayers (variable lis) state) #t) (error 'Redefining "Variable Already Exists"))
      ((null? (assignStatement lis)) (declare (variable lis) state flag))
      (else (declareAndAssign (variable lis) (assignStatement lis) state flag)))))


(define first car)
(define second cdr)

; declare updates the state with the new variable
;   and sets its value to '(), or null.
(define declare
  (lambda (var state flag)
    (cond
      ((eq? #t flag) (cons (cons (list '() var) (first state)) (second state)))
      ((null? state) (list (list '() var)))
      (else (cons (list '() var) state)))))


; declareAndAssign updates the state with the new variable and sets its value to the assignment statement.
; To determine if the var is type boolean or integer, we call the helper method, type.
(define declareAndAssign
  (lambda (var expr state flag)
    (cond
      ((and (eq? (type (operator expr)) #t) (eq? #t flag))  (cons (cons (list (Mboolean (operator expr) state) var) (first state)) (second state)))
      ((and (eq? (type (operator expr)) #f) (eq? #t flag))  (cons (cons (list (Minteger (operator expr) state) var) (first state)) (second state)))
      ((eq? (type (operator expr)) #t) (cons (list (Mboolean (operator expr) state) var) state))
      (else (cons (list (Minteger (operator expr) state) var) state)))))


(define assignmentStatement caddr)

; M_State for variable assignment, requires helper function assign
(define M_State_Assignment
  (lambda (lis state)
    (assign (variable lis) (assignmentStatement lis) state state)))


(define firstVar car)
(define firstPair car)
(define trailingPairs cdr)


; assign first checks if a variable exists with the respective name.
; If it does not exist, we return an error.
; If it does exist, we run helper function type to see if it is a boolean or integer, and then bind the value to the var.
(define assign
  (lambda (var expr state state2)
    (cond
      ((null? state) (error 'UnknownVar " Variable Does Not Exist"))
      ((eq? #f (varLookupLayers var state2)) (error 'UnknownVar " Variable Does Not Exist"))      
      ((null? (car state)) (cons '() (assign var expr (cdr state) (cdr state))))
      ((not (list? (caar state))) (assign var expr (list state) state2))
      ((and (lookupInLayer var (first state)) (type expr))       (replaceInLayerBool var expr state state2))
      ((and (lookupInLayer var (first state)) (not (type expr))) (replaceInLayerInt var expr (firstPair state) state2))
      (else                                               (cons (firstPair state) (assign var expr (trailingPairs state) state2))))))


(define lower cdr)
(define inner cadar)

; lookupInLayer checks if the respective var is in scope in the current layer.
; If it is not in scope in the first layer, it will check the next inner layer.
(define lookupInLayer
  (lambda (var layer)
    (cond
    ((null? layer) #f)
    ((eq? #f (M_Var_Lookup var (list (first layer)))) (M_Var_Lookup var (lower layer)))
    (else (M_Var_Lookup var (list (first layer)))))))

; replaceInLayerBool will replace the value of the respective boolean var in a specified layer.
(define replaceInLayerBool
  (lambda (var expr layer env)
    (cond
      ((and (eq? var (inner layer))      (cons (list (Mboolean expr env) var) (trailingPairs layer))))
      (else                                 (cons (firstPair layer) (assign var expr (trailingPairs layer) env))))))

; replaceInLayerBool will replace the value of the respective integer var in a specified layer.
(define replaceInLayerInt
  (lambda (var expr layer env)
    (cond
      ((and (eq? var (inner layer))      (cons (list (Minteger expr env) var) (trailingPairs layer))))
      (else                                 (cons (firstPair layer) (assign var expr (trailingPairs layer) env))))))

; Type is a helper function that determines if we use Mboolean or Minterger upon variable assignment.
; A result of true means the type is Boolean
; A result of false means the type is Integer
(define type
  (lambda (expr)
    (cond
      ((and (not (list? expr))
            (not (or (eq? expr 'true)
                     (eq? expr 'false)))) #f)     
      ((eq? expr 'true)          #t)
      ((eq? expr 'false)         #t)
      ((eq? (operator expr) '||) #t)
      ((eq? (operator expr) '&&) #t)
      ((eq? (operator expr) '!)  #t)
      ((eq? (operator expr) '<)  #t)
      ((eq? (operator expr) '<=) #t)
      ((eq? (operator expr) '>)  #t)
      ((eq? (operator expr) '>=) #t)
      ((eq? (operator expr) '!=) #t)
      ((eq? (operator expr) '==) #t)
      (else #f))))


(define firstValue caar)
(define varia cadar)

; M_Var_Lookup is a helper function to make sure a variable is not redefined.
; Returns true if the variable already exists and false if it does not.
(define M_Var_Lookup
  (lambda (var state)
    (cond
      ((null? state)                    #f)
      ((eq? var (varia state))          #t)
      (else                             (M_Var_Lookup var (trailingPairs state))))))

; varLookupLayers is also required to determine if a var is in scope in the current layer or not.
(define varLookupLayers
  (lambda (var layers)
    (cond
      ((null? layers) #f)
      ((null? (first layers)) (varLookupLayers var (second layers)))
      ((not (list? (firstValue layers))) (M_Var_Lookup var layers))
      ((null? (second layers)) (M_Var_Lookup var layers))
      ((eq? #f (M_Var_Lookup var (first layers))) (varLookupLayers var (second layers)))
      (else (M_Var_Lookup var (first layers))))))


  
(define vari cadar)

; M_Value_Lookup is for getting the value of a variable in the state
; If we hit the end of the state, it returns an error
; If we find the variable but its value is still '(), we
;   return an error because it is not assigned a value
; If we find the var with a value then we return the value
; Or else we call it recursively on the rest of the state
(define M_Value_Lookup
  (lambda (var state)
    (cond
      ((null? state)                    #f)
      ((and (eq? var (vari state))
            (null? (firstValue state))) (error 'UnknownVal "Value Not Defined"))
      ((eq? var (vari state))       (firstValue state))
      (else                             (M_Value_Lookup var (trailingPairs state))))))

; lookupStates returns the current state at the time of return.
; It uses the M_Value_Lookup function.
(define lookupStates
  (lambda (var layers)
    (cond
      ((null? (first layers)) (lookupStates var (second layers)))
      ((not (list? (firstValue layers))) (M_Value_Lookup var layers))
      ((null? (second layers)) (M_Value_Lookup var (first layers)))
      ((eq? #f (M_Value_Lookup var (first layers))) (lookupStates var (list (second layers))))
      (else (M_Value_Lookup var (first layers))))))

; M_State when the interpreter finds 'return as the first term
; Calls a helper function finalReturn which takes the final state after
;   return has been assigned a value in the state
(define M_State_Return
  (lambda (expr state)
    (cond
      ((null? (first state)) (M_State_Return expr (second state)))
      ((list? (first expr)) (evaluateExpression (first expr) state))
      ((eq? (lookupStates (first expr) (list state)) #t) 'true)
      ((eq? (lookupStates (first expr) (list state)) #f) (error 'UnknownVar "Variable not in scope"))
      (else                                (lookupStates (first expr) (list state))))))

; evaluateExpression determines if an expression is of type boolean or integer.
; It uses the helper function type.
(define evaluateExpression
  (lambda (expr state)
    (cond
      ((eq? #f (type expr)) (Minteger expr state))
      (else (Mboolean expr state)))))

; Helper function to return the final value
; If the value is a boolean then it chages it to true or false
(define finalReturn
  (lambda (expr state)
    (cond
    ((eq? (lookupStates 'return state) #t) 'true)
    ((eq? (lookupStates 'return state) #f) 'false)
    (else                                    (lookupStates 'return state)))))


(define firstWord car)
(define condition cadr)
(define ifStatement caddr)
(define elseStatement cdddr)

; M_State for if statement
; If the first term is if, then we check if the condition is true
;   If condition is true, then we call interpreter on the statement with the state
;   If not, we call M_State_If with the else statement because it could be another if
;   But if it's an else, we call interpreter on the else statement
(define M_State_If
  (lambda (lis state continue return break throw flag)
    (cond
      ((null? lis) state)
      ((not (eq? (firstWord lis) 'if))                 (interpreter lis state continue return break throw flag))
      ((and (eq? (firstWord lis) 'if)
            (eq? (Mboolean (condition lis) state) #t)) (interpreter (list (ifStatement lis)) state continue return break throw flag))
      (else                                            (M_State_If (elseStatement lis) state continue return break throw flag)))))


(define whileStatement cddr)

; M_State for a while loop
; If the condition is true, we call the M_State_While again with the condition/body
;   but the state is updated by calling interpreter on the while statement
; If the condition is false we retrun the state
(define M_State_While
  (lambda (lis state continue return break throw flag)
    (cond
      ((eq? #t (Mboolean (condition lis) state)) (M_State_While lis (call/cc (lambda (k) (interpreter (whileStatement lis) state k return break throw flag))) continue return break throw flag))
      (else state))))


(define operator car)
(define leftOperand cadr)
(define rightOperand caddr)
(define rightOperandList cddr)

; Takes a expression and returns an integer 
(define Minteger
  (lambda (expression state)
    (cond
      ((number? expression)                         expression)
      ((not (list? expression))                    (lookupStates expression state))
      ((eq? (operator expression) '+)              (+ (Minteger (leftOperand expression) state)
                                                      (Minteger (rightOperand expression) state)))
      ((and (eq? (operator expression) '-)
            (null? (rightOperandList expression))) (- 0 (Minteger (leftOperand expression) state)))
      ((eq? (operator expression) '-)              (- (Minteger (leftOperand expression) state)
                                                      (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '*)              (* (Minteger (leftOperand expression) state)
                                                      (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '/)              (quotient (Minteger (leftOperand expression) state)
                                                             (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '%)              (remainder (Minteger (leftOperand expression) state)
                                                              (Minteger (rightOperand expression) state)))
      (else (error 'UnknownOp " Bad Operator")))))

; Takes an expression and returns #t or #f
(define Mboolean
  (lambda (expression state)
    (cond
      ((eq? expression 'true) #t)
      ((eq? expression 'false) #f)
      ((not (list? expression))                     (lookupStates expression state))
      ((eq? (operator expression) '!)               (not (Mboolean (leftOperand expression) state)))
      ((eq? (operator expression) '&&)              (and (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((eq? (operator expression) '||)              (or  (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((eq? (operator expression) '!)               (not (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '!=)
            (eq? (rightOperand expression) 'true))  (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '!=)
            (eq? (leftOperand expression) 'true))   (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '!=)
            (eq? (rightOperand expression) 'false)) (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '!=)
            (eq? (leftOperand expression) 'false))  (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((eq? (operator expression) '!=)              (not (eq? (Minteger (leftOperand expression) state)
                                                              (Minteger (rightOperand expression) state))))
      ((and (eq? (operator expression) '==)
            (eq? (rightOperand expression) 'true))  (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '==)
            (eq? (leftOperand expression) 'true))   (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '==)
            (eq? (rightOperand expression) 'false)) (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((and (eq? (operator expression) '==)
            (eq? (leftOperand expression) 'false))  (eq? (Mboolean (leftOperand expression) state)
                                                         (Mboolean (rightOperand expression) state)))
      ((eq? (operator expression) '==)              (eq? (Minteger (leftOperand expression) state)
                                                         (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '<)               (<   (Minteger (leftOperand expression) state)
                                                         (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '>)               (>   (Minteger (leftOperand expression) state)
                                                         (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '<=)              (<=  (Minteger (leftOperand expression) state)
                                                         (Minteger (rightOperand expression) state)))
      ((eq? (operator expression) '>=)              (>=  (Minteger (leftOperand expression) state)
                                                         (Minteger (rightOperand expression) state)))
      (else (error 'UnknownOp " Bad Operator")))))