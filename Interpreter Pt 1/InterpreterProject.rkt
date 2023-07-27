#lang racket
(require "simpleParser.rkt")

; Simple Language Interpreter Project
; Carter Chen
; Victor Majestic
; Matthew Vatne

; interpret calls our interpreter with the initial state
; the state consists of a list of pairs, and it is ordered as '((value1 var1) (value2 var2) ...)
(define interpret
  (lambda (filename)
    (interpreter (parser filename) '((() return)))))


(define firstTerm caar)
(define rightSubtree cdr)
(define leftSubtree car)
(define returnExpr cdar)

; the interpreter function looks at the first term in the left subtree
;   and calls interpreter on the right subtree and the appropriate M_State
;   on the left subtree which is used as the state for the recursive call
(define interpreter
  (lambda (lis state)
    (cond
      ((null? lis) state)
      ((equal? (firstTerm lis) 'var)    (interpreter    (rightSubtree lis) (M_State_Declaration (leftSubtree lis) state)))
      ((equal? (firstTerm lis) '=)      (interpreter    (rightSubtree lis) (M_State_Assignment (leftSubtree lis) state)))
      ((equal? (firstTerm lis) 'return) (M_State_Return (returnExpr lis) state state))
      ((equal? (firstTerm lis) 'if)     (interpreter    (rightSubtree lis) (M_State_If (leftSubtree lis) state)))
      ((equal? (firstTerm lis) 'while)  (interpreter    (rightSubtree lis) (M_State_While (leftSubtree lis) state)))
      (else (error 'UnknownTerm "Unknown Term in Syntax Tree")))))


(define assignStatement cddr)
(define variable cadr)

; M_State for declaring a variable
; First checks to make sure a variable is not being redefined, if so returns error
; If not, then checks to see if we are assigning a value also
;   If so, then we call declareAndAssign on the var and assignment value using the state
;   If not, then we call declare on the var using the state
(define M_State_Declaration
  (lambda (lis state)
    (cond
      ((eq? (M_Var_Lookup (variable lis) state) #t) (error 'Redefining "Variable Already Exists"))
      ((null? (assignStatement lis)) (declare (variable lis) state))
      (else (declareAndAssign (variable lis) (assignStatement lis) state)))))


; declare updates the state with the new variable
;   and sets its value to '()
(define declare
  (lambda (var state)
      (cons (list '() var) state)))


; declareAndAssign updates the state with the new variable
;   and sets its value to the assignment statement
; To determine if the var is type boolean or integer, we call the helper method type
(define declareAndAssign
  (lambda (var expr state)
    (cond
      ((eq? (type (operator expr)) #t)   (cons (list (Mboolean (operator expr) state) var) state))
      (else (not (type (operator expr))) (cons (list (Minteger (operator expr) state) var) state)))))


(define assignmentStatement caddr)

; M_State for assigning a value to a variable
;   Calls helper function assign 
(define M_State_Assignment
  (lambda (lis state)
    (assign (variable lis) (assignmentStatement lis) state state)))


(define firstVar cadar)
(define firstPair car)
(define trailingPairs cdr)

; Runs through the state and checks of there is a variable with the name in it
;   If not and it hits the en dof the state, then it returns an error because it is an unknown variable
;   If the var matches a variable in the state, then it is updated using Mboolean or
;      Minterger depending on what type returns
(define assign
  (lambda (var expr state state2)
    (cond
      ((null? state) (error 'UnknownVar " Variable Does Not Exist"))
      ((and (eq? var (firstVar state)) (type expr))       (cons (list (Mboolean expr state2) var) (trailingPairs state)))
      ((and (eq? var (firstVar state)) (not (type expr))) (cons (list (Minteger expr state2) var) (trailingPairs state)))
      (else                                               (cons (firstPair state) (assign var expr (trailingPairs state) state2))))))


; Type is a helper function that determines if we use Mboolean or Minterger
;   when assigning a value
; If it is Mboolean, type witll return true
; Otherwise it will return false
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

; Helper function to make sure a variable is not redefined
; Returns true if the variable already exists and false if it does not
(define M_Var_Lookup
  (lambda (var state)
    (cond
      ((null? state)                    #f)
      ((eq? var (firstVar state))       #t)
      (else                             (M_Var_Lookup var (trailingPairs state))))))

; M_Value_Lookup is for getting the value of a variable in the state
; If we hit the end of the state, it returns an error
; If we find the variable but its value is still '(), we
;   return an error because it is not assigned a value
; If we find the var with a value then we return the value
; Or else we call it recursively on the rest of the state
(define M_Value_Lookup
  (lambda (var state)
    (cond
      ((null? state)                    (error 'UnknownVar " Variable Does Not Exist"))
      ((and (eq? var (firstVar state))
            (null? (firstValue state))) (error 'UnknownVal "Value Not Defined"))
      ((eq? var (firstVar state))       (firstValue state))
      (else                             (M_Value_Lookup var (trailingPairs state))))))


; M_State when the interpreter finds 'return as the first term
; Calls a helper function finalReturn which takes the final state after
;   return has been assigned a value in the state
(define M_State_Return
  (lambda (expr state state2)
      (finalReturn (assign 'return (operator expr) state state2))))


; Helper function to return the final value
; If the value is a boolean then it chages it to true or false
(define finalReturn
  (lambda (state)
    (cond
    ((eq? (M_Value_Lookup 'return state) #t) (display "true"))
    ((eq? (M_Value_Lookup 'return state) #f) (display "false"))
    (else                                    (M_Value_Lookup 'return state)))))


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
  (lambda (lis state)
    (cond
      ((null? lis) state)
      ((not (eq? (firstWord lis) 'if))                 (interpreter lis state))
      ((and (eq? (firstWord lis) 'if)
            (eq? (Mboolean (condition lis) state) #t)) (interpreter (list (ifStatement lis)) state))
      (else                                            (M_State_If (elseStatement lis) state)))))


(define whileStatement cddr)

; M_State for a while loop
; If the condition is true, we call the M_State_While again with the condition/body
;   but the state is updated by calling interpreter on the while statement
; If the condition is false we retrun the state
(define M_State_While
  (lambda (lis state)
    (cond
      ((eq? #t (Mboolean (condition lis) state)) (M_State_While lis (interpreter (whileStatement lis) state)))
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
      ((not (list? expression))                    (M_Value_Lookup expression state))
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
      ((not (list? expression))                     (M_Value_Lookup expression state))
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