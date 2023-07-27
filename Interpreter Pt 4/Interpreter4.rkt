#lang racket
; If you are using scheme instead of racket, comment these two lines, uncomment the (load "simpleParser.scm") and comment the (require "simpleParser.rkt")
(require "classParser.rkt")


; An interpreter for the simple language that uses call/cc for the continuations.  Does not handle side effects.
(define call/cc call-with-current-continuation)


; The functions that start interpret-...  all return the current environment.
; The functions that start eval-...  all return a value

; The main function.  Calls parser to get the parse tree and interprets it with a new environment.  The returned value is in the environment.
(define interpret
  (lambda (file className)
    (scheme->language
     (call/cc
      (lambda (return)
        (interpret-statement-list (parser file) (string->symbol className) (newenvironment) return
                                  (lambda (env) (myerror "Break used outside of loop")) (lambda (env) (myerror "Continue used outside of loop"))
                                  (lambda (v env) (myerror "Uncaught exception thrown"))
                                   (lambda (v) v) (lambda (v) v)))))))


(define rightSubtree cdr)
(define leftSubtree car)

; interprets a list of statements.  The environment from each statement is used for the next ones.
; when the statement list is null, it interprets the main function
(define interpret-statement-list
  (lambda (statement-list className environment return break continue throw compileType this)
    (if (null? statement-list)
        ;environment -> Used for debugging 
        (eval-mainClass className environment return break continue throw compileType this)
        (interpret-statement-list (rightSubtree statement-list) className (interpret-statement (leftSubtree statement-list) environment return break continue throw compileType this) return break continue throw compileType this))))

; *An example of how the functionParser parses an example program*
; ((function fib (a) ((if (== a 0) (return 0) (if (== a 1) (return 1) (return (+ (funcall fib (- a 1)) (funcall fib (- a 2))))))))
;    (function main () ((return (funcall fib 10)))))

(define statements cadr)

; interpret a statement in the environment with continuations for return, break, continue, throw
(define interpret-statement
  (lambda (statement environment return break continue throw compileType this)
    (cond
      ((eq? 'new (statement-type statement)) (interpret-new (body statement) environment return break continue throw compileType this))
      ((eq? 'class (statement-type statement)) (interpret-class (body statement) environment))
      ((or (eq? 'static-function (statement-type statement)) (eq? 'function (statement-type statement))) (interpret-function statement environment return break continue throw compileType this))
      ((eq? 'funcall (statement-type statement)) (interpret-funcall_M_State (statements (lookup (functionName (body statement)) environment))
                                                                                        (insert_params_in_environment (car (lookup (functionName (body statement)) environment)) (cdr (cdr statement)) (push-frame environment) throw)
                                                                                        return break continue throw compileType this))
      ((eq? 'return (statement-type statement)) (interpret-return statement environment throw return compileType this))
      ((eq? 'var (statement-type statement)) (interpret-declare statement environment return break continue throw compileType this))
      ((eq? '= (statement-type statement)) (interpret-assign statement environment throw compileType this))
      ((eq? 'if (statement-type statement)) (interpret-if statement environment return break continue throw compileType this))
      ((eq? 'while (statement-type statement)) (interpret-while statement environment return throw compileType this))
      ((eq? 'continue (statement-type statement)) (continue environment))
      ((eq? 'break (statement-type statement)) (break environment))
      ((eq? 'begin (statement-type statement)) (interpret-block statement environment return break continue throw compileType this))
      ((eq? 'throw (statement-type statement)) (interpret-throw statement environment throw compileType this))
      ((eq? 'try (statement-type statement)) (interpret-try statement environment return break continue throw compileType this))
      (else (myerror "Unknown statement:" (statement-type statement))))))

(define functionName car)
(define body cdr)
(define name car)
(define funcStatements cadr)
(define funcBody cddr)
(define funcName cadr)

; interprets the dot
(define interpret-dot
  (lambda (name field env throw)
    (cond
      ((null? name) (myerror "Null instance name"))
      ((null? field) (myerror "Null instance field"))
      ((eq? name 'this) (eval-expression field (pop-frame env) throw))
      ((eq? name 'super) (eval-expression field (pop-frame (pop-frame env)) throw))
      (else (eval-expression field (append (lookup name env) env) throw)))))

; interprets the class
(define interpret-class
  (lambda (closure environment)
    (if (not (null? closure))
        (insert (name closure) (body closure) environment)
        (myerror "No closure"))))

; interprets new object
(define interpret-new
  (lambda (statement environment return break continue throw compileType this)
    (if (not (null? statement))
        (if (null? (lookup (cadadr statement) environment))
            (myerror "Class does not exist")
            (insert (car statement) (instanceFields-stateLayer (cadr (lookup (cadadr statement) environment))
                                                               (newenvironment)
                                                               return break continue throw compileType this)
                    environment))
        (myerror "Statement does not exist"))))


; Function to run when the environemnt is finished
; If the main exists in the environment, then we interpret the body statements in the main
; If not, then we throw an error
(define eval-mainClass
  (lambda (className environment return break continue throw compileType this)
    (if (exists? className environment)
      (interpret-statement-list (funcStatements (lookup-function (funcStatements (lookup className environment)) 'main))
                                className
                                (instanceFields-stateLayer (cadr (lookup className environment)) (push-frame environment) return break continue throw compileType this)
                                return break continue throw compileType this) 
      (myerror "Class does not exist"))))

; creates instance fields from the state layer
(define instanceFields-stateLayer
  (lambda (closure environment return break continue throw compileType this)
    (if (not (null? closure))
        (cond
          ((list? (car closure))
            (instanceFields-stateLayer (cdr closure)
                                       (interpret-statement (car closure) environment return break continue throw compileType this)
                                       return break continue throw compileType this))
          (else (interpret-statement closure environment return break continue throw compileType this)))
         environment)))

; looks up a function and returns the function closure
(define lookup-function
  (lambda (closure name)
    (if (not (null? closure))
        (cond
          ((eq? name (cadar closure)) (cddar closure))
          (else (lookup-function (cdr closure) name)))
        (myerror "Function does not exist"))))

; Denotational semantics for a function definition
; 1) Create the closure for the function
; 2) Bind it to the function name
; If the function's body is not null, the we do that by inserting the function name in the statement
;    to the function body of the statement in the environment
(define interpret-function
  (lambda (statement environment return break continue throw compileType this)
    (if (not (null? (funcBody statement)))
      (insert (funcName statement) (funcBody statement) environment) 
       environment))) 


; Denotational semantics for a function call
; 1) Look up funcation name in the active state to get the closure
; 2) Run the function in the closure to get the function state for the function call
; 3) Add a new layer to the function's state (done in interpret-statement)
; 4) Evaluate actual parameters in current state
; 4b) Bind value to the formal formal parameters in the function's state
; 5) Create continuations for the function's body
; ** Create a retrun continuation to jump back to on return
; ** Done using call/cc here
; 6) Call M_State on the function body with the function state and new continuations
; 7) On return, update the current state with values from the function state
(define interpret-funcall_M_State
 (lambda (statements environment return break continue throw compileType this)
  (cond
    ((null? statements) environment)
    (else
     (cond
       ((not (list? (call/cc (lambda (break_return) (interpret-statement (leftSubtree statements) environment break_return break continue throw compileType this)))))
             environment)
       (else (interpret-funcall_M_State (rightSubtree statements) (call/cc (lambda (break_return)
                                                                         (interpret-statement (leftSubtree statements) environment break_return break continue throw compileType this)))
                                         return break continue throw compileType this)))))))


; Is called when funcall is considered an operator and must be evaluated
; Checks to see if the function name that is being called exists, if not then an error is throw
; If it does exists, checks if the is the statements of funcall is null
; If not, then we call interpret-block-list on the statements of the funcall and use an updated environment with a new return continuation,
;   popping a frame after we are done
;   which is similar to the above funcall
; If not parameters need to be added, then we pop then push a frame on and call interpret-block-list
(define eval-funcall
  (lambda (funcall environment throw)
    (call/cc
     (lambda (functionReturn)
          (if (list? (car funcall)) ; to see if there is dot
              (pop-frame (interpret-block-list (cadr (lookup (caddar funcall) (lookup (cadar funcall) environment)))
                                               (insert_params_in_environment (car (lookup (caddar funcall) (lookup (cadar funcall) environment)))
                                                                             (cdr funcall)
                                                                             (push-frame (append (lookup (cadar funcall) environment) environment))
                                                                             throw)
                                               functionReturn
                                               (lambda (env) (myerror "Break used outside of loop"))
                                               (lambda (env) (myerror "Continue used outside of loop"))
                                               throw (lambda (v) v) (lambda (v) v)))
              (cond
                (not (exists? (functionName funcall)) (myerror "Function does not exist"))
                (else
                 (if (not (null? (cdr funcall)))      
                  (pop-frame (interpret-block-list (funcStatements (lookup (functionName funcall) environment))
                                                   (insert_params_in_environment (functionName (lookup (functionName funcall) environment)) (cdr funcall) (push-frame environment) throw)
                                                   functionReturn
                                                   (lambda (env) (myerror "Break used outside of loop"))
                                                   (lambda (env) (myerror "Continue used outside of loop"))
                                                   throw (lambda (v) v) (lambda (v) v)))
                  (pop-frame (interpret-block-list (funcStatements (lookup (functionName funcall) environment))
                                                   (push-frame (pop-frame environment))
                                                   functionReturn
                                                   (lambda (env) (myerror "Break used outside of loop"))
                                                   (lambda (env) (myerror "Continue used outside of loop"))
                                                   throw (lambda (v) v) (lambda (v) v)))))
                ))))))


; Helper method for adding paraments to the environment
; 1) Checks iif there are no parameter names, if so then returns the environment
; 2) Checks to see if there is the same amount of names with values by using built-in length function
;   3) If so, then we check whether or not the parameter names is a list
;   4) If it is a list, then we run insert_param_in_environment on the cdr of the lists and the new environment
;   5) If not a list, then we insert the parameter names and evaluate the expressions of the values and pop the frame of the environment
(define insert_params_in_environment
  (lambda (parameterNames parameterValues environment throw)
    (cond
      ((null? parameterNames) environment)
      ((eq? (length parameterNames) (length parameterValues))
            (if (list? parameterNames)
              (insert_params_in_environment (cdr parameterNames) (cdr parameterValues) (insert (first parameterNames) (eval-expression (first parameterValues) (pop-frame environment) throw) environment) throw)
              (insert parameterNames (eval-expression parameterValues (pop-frame environment)) environment)))
      (else (myerror "Mismatching params and args")))))


; This is for interpreting a block, can be function call or try/catch block or regular block
; It is copy/pasted from interpret-statement-list, but
;   the difference is that if the statement-list is null
;   then the environment will be returned instead of running the main function
(define interpret-block-list
  (lambda (statement-list environment return break continue throw compileType this)
    (if (null? statement-list)
        environment
        (interpret-block-list (rightSubtree statement-list) (interpret-statement (leftSubtree statement-list) environment return break continue throw compileType this) return break continue throw compileType this))))




; Calls the return continuation with the given expression value
(define interpret-return
  (lambda (statement environment throw return compileType this)
    (return (eval-expression (get-expr statement) environment throw))))

; Adds a new variable binding to the environment.  There may be an assignment with the variable
(define interpret-declare
  (lambda (statement environment return break continue throw compileType this)
    (if (exists-declare-value? statement)
        (if (not (list? (get-declare-value statement)))
            (insert (get-declare-var statement) (eval-expression (get-declare-value statement) environment throw) environment)
            (interpret-new (cdr statement) environment return break continue throw compileType this))
        (insert (get-declare-var statement) 'novalue environment))))

; Updates the environment to add an new binding for a variable
(define interpret-assign
  (lambda (statement environment throw compileType this)
    (if (list? (get-assign-lhs statement))
        (cond
          ;((eq? (cadadr statement) 'super) 0)
          ((eq? (cadadr statement) 'this) (update (car (cddadr statement)) (eval-expression (caddr statement) environment throw) (pop-frame environment)))
          (else (myerror "Error: Unknown syntax")))
        (update (get-assign-lhs statement) (eval-expression (get-assign-rhs statement) environment throw) environment))))

; We need to check if there is an else condition.  Otherwise, we evaluate the expression and do the right thing.
(define interpret-if
  (lambda (statement environment return break continue throw compileType this)
    (cond
      ((eval-expression (get-condition statement) environment throw) (interpret-statement (get-then statement) environment return break continue throw compileType this))
      ((exists-else? statement) (interpret-statement (get-else statement) environment return break continue throw compileType this))
      (else environment))))

; Interprets a while loop.  We must create break and continue continuations for this loop
(define interpret-while
  (lambda (statement environment return throw compileType this)
    (call/cc
     (lambda (break)
       (letrec ((loop (lambda (condition body environment)
                        (if (eval-expression condition environment throw)
                            (loop condition body (interpret-statement body environment return break (lambda (env) (break (loop condition body env))) throw compileType this))
                         environment))))
         (loop (get-condition statement) (get-body statement) environment))))))


; Interprets a block.  The break, continue, and throw continuations must be adjusted to pop the environment
(define interpret-block
  (lambda (statement environment return break continue throw compileType this)
    (pop-frame (interpret-block-list (cdr statement)
                                         (push-frame environment)
                                         return
                                         (lambda (env) (break (pop-frame env)))
                                         (lambda (env) (continue (pop-frame env)))
                                         (lambda (v env) (throw v (pop-frame env)))
                                          compileType this))))

; We use a continuation to throw the proper value. Because we are not using boxes, the environment/state must be thrown as well so any environment changes will be kept
(define interpret-throw
  (lambda (statement environment throw compileType this)
    (throw (eval-expression (get-expr statement) environment throw) environment)))

; Interpret a try-catch-finally block

; Create a continuation for the throw.  If there is no catch, it has to interpret the finally block, and once that completes throw the exception.
;   Otherwise, it interprets the catch block with the exception bound to the thrown value and interprets the finally block when the catch is done
(define create-throw-catch-continuation
  (lambda (catch-statement environment return break continue throw jump finally-block)
    (cond
      ((null? catch-statement) (lambda (ex env) (throw ex (interpret-block finally-block env return break continue throw)))) 
      ((not (eq? 'catch (statement-type catch-statement))) (myerror "Incorrect catch statement"))
      (else (lambda (ex env)
              (jump (interpret-block finally-block
                                     (pop-frame (interpret-block-list 
                                                 (get-body catch-statement) 
                                                 (insert (catch-var catch-statement) ex (push-frame env))
                                                 return 
                                                 (lambda (env2) (break (pop-frame env2))) 
                                                 (lambda (env2) (continue (pop-frame env2))) 
                                                 (lambda (v env2) (throw v (pop-frame env2)))))
                                     return break continue throw)))))))

; To interpret a try block, we must adjust  the return, break, continue continuations to interpret the finally block if any of them are used.
;  We must create a new throw continuation and then interpret the try block with the new continuations followed by the finally block with the old continuations
(define interpret-try
  (lambda (statement environment return break continue throw compileType this)
    (call/cc
     (lambda (jump)
       (let* ((finally-block (make-finally-block (get-finally statement)))
              (try-block (make-try-block (get-try statement)))
              (new-return (lambda (v) (begin (interpret-block finally-block environment return break continue throw) (return v))))
              (new-break (lambda (env) (break (interpret-block finally-block env return break continue throw))))
              (new-continue (lambda (env) (continue (interpret-block finally-block env return break continue throw))))
              (new-throw (create-throw-catch-continuation (get-catch statement) environment return break continue throw jump finally-block)))
         (interpret-block finally-block
                          (interpret-block try-block environment new-return new-break new-continue new-throw)
                          return break continue throw))))))

; helper methods so that I can reuse the interpret-block method on the try and finally blocks
(define make-try-block
  (lambda (try-statement)
    (cons 'begin try-statement)))

(define make-finally-block
  (lambda (finally-statement)
    (cond
      ((null? finally-statement) '(begin))
      ((not (eq? (statement-type finally-statement) 'finally)) (myerror "Incorrectly formatted finally block"))
      (else (cons 'begin (cadr finally-statement))))))

; Evaluates all possible boolean and arithmetic expressions, including constants and variables.
(define eval-expression
  (lambda (expr environment throw)
    (cond
      ((number? expr) expr)
      ((eq? expr 'true) #t)
      ((eq? expr 'false) #f)
      ((not (list? expr)) (lookup expr environment))
      (else (eval-operator expr environment throw)))))

; Evaluate a binary (or unary) operator.  Although this is not dealing with side effects, I have the routine evaluate the left operand first and then
; pass the result to eval-binary-op2 to evaluate the right operand.  This forces the operands to be evaluated in the proper order in case you choose
; to add side effects to the interpreter
(define eval-operator
  (lambda (expr environment throw)
    (cond
      ((eq? (operator expr) 'dot) (interpret-dot (cadr expr) (caddr expr) environment throw))
      ((eq? '! (operator expr)) (not (eval-expression (operand1 expr) environment throw)))
      ((and (eq? '- (operator expr)) (= 2 (length expr))) (- (eval-expression (operand1 expr) environment throw)))
      (else (eval-binary-op2 expr (eval-expression (operand1 expr) environment throw) environment throw)))))

; Complete the evaluation of the binary operator by evaluating the second operand and performing the operation.
(define eval-binary-op2
  (lambda (expr op1value environment throw)
    (cond
      ((eq? 'funcall (operator expr)) (eval-funcall (cdr expr) environment throw))
      ((eq? '+ (operator expr)) (+ op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '- (operator expr)) (- op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '* (operator expr)) (* op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '/ (operator expr)) (quotient op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '% (operator expr)) (remainder op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '== (operator expr)) (isequal op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '!= (operator expr)) (not (isequal op1value (eval-expression (operand2 expr) environment throw))))
      ((eq? '< (operator expr)) (< op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '> (operator expr)) (> op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '<= (operator expr)) (<= op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '>= (operator expr)) (>= op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '|| (operator expr)) (or op1value (eval-expression (operand2 expr) environment throw)))
      ((eq? '&& (operator expr)) (and op1value (eval-expression (operand2 expr) environment throw)))
      (else (myerror "Unknown operator:" (operator expr))))))

; Determines if two values are equal.  We need a special test because there are both boolean and integer types.
(define isequal
  (lambda (val1 val2)
    (if (and (number? val1) (number? val2))
        (= val1 val2)
        (eq? val1 val2))))


;-----------------
; HELPER FUNCTIONS
;-----------------
; These helper functions define the operator and operands of a value expression
(define operator car)
(define operand1 cadr)
(define operand2 caddr)
(define operand3 cadddr)

(define exists-operand2?
  (lambda (statement)
    (not (null? (cddr statement)))))

(define exists-operand3?
  (lambda (statement)
    (not (null? (cdddr statement)))))

; these helper functions define the parts of the various statement types
(define statement-type operator)
(define get-expr operand1)
(define get-declare-var operand1)
(define get-declare-value operand2)
(define exists-declare-value? exists-operand2?)
(define get-assign-lhs operand1)
(define get-assign-rhs operand2)
(define get-condition operand1)
(define get-then operand2)
(define get-else operand3)
(define get-body operand2)
(define exists-else? exists-operand3?)
(define get-try operand1)
(define get-catch operand2)
(define get-finally operand3)

(define catch-var
  (lambda (catch-statement)
    (car (operand1 catch-statement))))


;------------------------
; Environment/State Functions
;------------------------

; create a new empty environment
(define newenvironment
  (lambda ()
    (list (newframe))))

; create an empty frame: a frame is two lists, the first are the variables and the second is the "store" of values
(define newframe
  (lambda ()
    '(() ())))

; add a frame onto the top of the environment
(define push-frame
  (lambda (environment)
    (cons (newframe) environment)))

; remove a frame from the environment
(define pop-frame
  (lambda (environment)
    (cdr environment)))

; some abstractions
(define topframe car)
(define remainingframes cdr)

; does a variable exist in the environment?
(define exists?
  (lambda (var environment)
    (cond
      ((null? environment) #f)
      ((exists-in-list? var (car (topframe environment))) #t)
      (else (exists? var (remainingframes environment))))))

; does a variable exist in a list?
(define exists-in-list?
  (lambda (var l)
    (cond
      ((null? l) #f)
      ((eq? var (car l)) #t)
      (else (exists-in-list? var (cdr l))))))

; Looks up a value in the environment.  If the value is a boolean, it converts our languages boolean type to a Scheme boolean type
(define lookup
  (lambda (var environment)
    (lookup-variable var environment)))
  
; A helper function that does the lookup.  Returns an error if the variable does not have a legal value
(define lookup-variable
  (lambda (var environment)
    (let ((value (lookup-in-env var environment)))
      (if (eq? 'novalue value)
          (myerror "error: variable without an assigned value:" var)
          value))))

; Return the value bound to a variable in the environment
(define lookup-in-env
  (lambda (var environment)
    (cond
      ((null? environment) (myerror "error: undefined variable" var))
      ((exists-in-list? var (car (topframe environment))) (lookup-in-frame var (topframe environment)))
      (else (lookup-in-env var (cdr environment))))))

; Return the value bound to a variable in the frame
(define lookup-in-frame
  (lambda (var frame)
    (cond
      ((not (exists-in-list? var (variables frame))) (myerror "error: undefined variable" var))
      (else (language->scheme (get-value (indexof var (variables frame)) (store frame)))))))

; Get the location of a name in a list of names
(define indexof
  (lambda (var l)
    (cond
      ((null? l) 0)  ; should not happen
      ((eq? var (car l)) 0)
      (else (+ 1 (indexof var (cdr l)))))))

; Get the value stored at a given index in the list
(define get-value
  (lambda (n l)
    (cond
      ((zero? n) (car l))
      (else (get-value (- n 1) (cdr l))))))

; Adds a new variable/value binding pair into the environment.  Gives an error if the variable already exists in this frame.
(define insert
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (myerror "error: variable is being re-declared:" var)
        (cons (add-to-frame var val (car environment)) (cdr environment)))))

; Changes the binding of a variable to a new value in the environment.  Gives an error if the variable does not exist.
(define update
  (lambda (var val environment)
    (if (exists? var environment)
        (update-existing var val environment)
        (myerror "error: variable used but not defined:" var))))

; Add a new variable/value pair to the frame.
(define add-to-frame
  (lambda (var val frame)
    (list (cons var (variables frame)) (cons (scheme->language val) (store frame)))))

; Changes the binding of a variable in the environment to a new value
(define update-existing
  (lambda (var val environment)
    (if (exists-in-list? var (variables (car environment)))
        (cons (update-in-frame var val (topframe environment)) (remainingframes environment))
        (cons (topframe environment) (update-existing var val (remainingframes environment))))))

; Changes the binding of a variable in the frame to a new value.
(define update-in-frame
  (lambda (var val frame)
    (list (variables frame) (update-in-frame-store var val (variables frame) (store frame)))))

; Changes a variable binding by placing the new value in the appropriate place in the store
(define update-in-frame-store
  (lambda (var val varlist vallist)
    (cond
      ((eq? var (car varlist)) (cons (scheme->language val) (cdr vallist)))
      (else (cons (car vallist) (update-in-frame-store var val (cdr varlist) (cdr vallist)))))))

; Returns the list of variables from a frame
(define variables
  (lambda (frame)
    (car frame)))

; Returns the store from a frame
(define store
  (lambda (frame)
    (cadr frame)))

; Functions to convert the Scheme #t and #f to our languages true and false, and back.

(define language->scheme
  (lambda (v) 
    (cond 
      ((eq? v 'false) #f)
      ((eq? v 'true) #t)
      (else v))))

(define scheme->language
  (lambda (v)
    (cond
      ((eq? v #f) 'false)
      ((eq? v #t) 'true)
      (else v))))



; Because the error function is not defined in R5RS scheme, I create my own:
(define error-break (lambda (v) v))
(call-with-current-continuation (lambda (k) (set! error-break k)))

(define myerror
  (lambda (str . vals)
    (letrec ((makestr (lambda (str vals)
                        (if (null? vals)
                            str
                            (makestr (string-append str (string-append " " (symbol->string (car vals)))) (cdr vals))))))
      (error-break (display (string-append str (makestr "" vals)))))))

