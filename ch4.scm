(define apply-in-underlying-scheme apply)

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((make-unbound? exp) (eval-make-unbound! exp env))
        ((if? exp) (eval-if exp env))
        ((and? exp) (eval-and (cdr exp) env))
        ((or? exp) (eval-or (cdr exp) env))
        ((lambda? exp)
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp)
         (eval-sequence (begin-actions exp) env))
        ((let? exp) (eval (let->combination exp) env))
        ((let*? exp) (eval (let*->nested-lets exp) env))
        ((cond? exp) (eval (cond->if exp) env))
        ((application? exp)
         (begin
           (apply* (eval (operator exp) env)
                   (list-of-values (operands exp) env))))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (apply* procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence
          (procedure-body procedure)
          (extend-environment
           (procedure-parameters procedure)
           arguments
           (procedure-environment procedure))))
        (else
         (error "Unknown procedure type -- APPLY*" procedure))))

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-and exp env)
  (if (null? exp)
      'true
      (if (false? (eval (car exp) env))
          'false
          (eval-and (cdr exp) env))))

(define (eval-or exp env)
  (if (null? exp)
      'false
      (if (true? (eval (car exp) env))
          'true
          (eval-or (cdr exp) env))))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

(define (eval-make-unbound! exp env)
  (make-unbound! (cadr exp) env)
  'ok)

;; Expressions

(define (self-evaluating? exp)
  (cond ((number? exp) #t)
        ((string? exp) #t)
        (else #f)))

(define (variable? exp)
  (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp)
  (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (make-unbound? exp)
  (tagged-list? exp 'make-unbound!))

(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp)
  (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (and? exp) (tagged-list? exp 'and))
(define (or? exp) (tagged-list? exp 'or))

(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq)
  (if (pair? seq)
      (null? (cdr seq))
      'true))
(define (first-exp seq)
  (if (pair? seq)
      (car seq)
      seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))
(define (make-begin seq) (cons 'begin seq))

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->exp (cond-actions first))
                     (expand-clauses rest))))))

(define (let? exp)
  (begin
    (tagged-list? exp 'let)))
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (caddr exp))
(define (let-variables bindings) (map car bindings))
(define (let-values bindings) (map cadr bindings))
(define (let->combination exp)
  (let* ((bindings (let-bindings exp))
         (lam (make-lambda (let-variables bindings)
                           (list (let-body exp)))))
    (append (list lam) (let-values bindings))))

(define (let*? exp)
  (begin
    (tagged-list? exp 'let*)))
(define (let-variable binding) (car binding))
(define (let-value binding) (cadr binding))
(define (let*->nested-lets exp)
  (define (rec bindings body)
    (if (null? bindings)
        body
        (let* ((b (car bindings))
               (lam (make-lambda (list (let-variable b))
                                 (list (rec (cdr bindings) body)))))
          (append (list lam) (list (let-value b))))))
  (rec (let-bindings exp) (let-body exp)))

;; Predicates

(define (true? x)
  (not (eq? x #f)))
(define (false? x)
  (eq? x #f))

(define (make-procedure parameters body env)
  (list 'procedure parameters body env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

;; Environment, Bindings and Frames

;; Lexical scope - get the scope next highest
(define (enclosing-environment env) (cdr env))

;; Get the inner-most scope
(define (first-frame env) (car env))

;; Define an empty environment to start things off
(define the-empty-environment '())

;; Make a new frame with bindings from a list
;; of variables and values
(define (make-frame variables values)
  (if (null? variables)
      '()
      (cons (list (car variables) (car values))
            (make-frame (cdr variables) (cdr values)))))

;; Extract just the variables from a single frame's bindings
(define (frame-variables frame) (map car frame))

;; Extract just the values from a single frame's bindings
(define (frame-values frame) (map cadr frame))

;; Copy a list
;; TODO: this probably isn't the best way to handle
;; add-binding-to-frame using an associative list,
;; but I can't think else how to do it.
(define (list-copy l)
  (if (null? l)
      '()
      (cons (car l)
            (list-copy (cdr l)))))

;; Add a new binding to an existing frame (mutation)
(define (add-binding-to-frame! var val frame)
  (let ((old-frame (list-copy frame)))
    (set-car! frame (list var val))
    (set-cdr! frame old-frame)))

;; Add a new frame to an existing environment.
;; Adds to the front, so this is a more inner scope.
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

;; Variables

;; Recursively search a given environment for a variable's
;; bound value. Start at the innermost scope (first frame)
;; and proceed, throwing an error if no value is found.
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan bindings)
      (cond ((null? bindings)
             (env-loop (enclosing-environment env)))
            ((null? (car bindings))
             (scan (cdr bindings)))
            ((eq? var (caar bindings))
             (cadar bindings))
            (else (scan (cdr bindings)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (scan (first-frame env))))
  (env-loop env))

;; Give a variable a new value. Stops
;; at the first matching var (innermost frame/scope)
(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan bindings)
      (cond ((null? bindings)
             (env-loop (enclosing-environment env)))
            ((eq? var (caar bindings))
             (set-car! bindings (list (caar bindings) val)))
            (else (scan (cdr bindings)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (scan (first-frame env))))
  (env-loop env))

;; Add a new variable binding to the first frame
;; (innermost scope). If the variable already
;; exists in this frame, set it's value to val.
(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan bindings)
      (cond ((null? bindings)
             (add-binding-to-frame! var val frame)) ;; note frame, not bindings
            ((eq? var (caar bindings))
             (set-car! bindings (list (caar bindings) val)))
            (else (scan (cdr bindings)))))
    (scan frame)))

;; Un-bind an existing variable, only in current frame
(define (make-unbound! var env)
  (define (scan bindings)
    (cond ((null? bindings)
           (error "No such variable to undefine." var))
          ((eq? var (caar bindings))
           (set-car! bindings '()))
          (else (scan (cdr bindings)))))
  (let ((frame (first-frame env)))
    (if (null? frame)
        (error "Nothing to undefine, frame is empty")
        (scan frame))))

;; Primitive Functions/Procedures

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cadr cadr)
        (list 'cdar cdar)
        (list 'caar caar)
        (list 'cddr cddr)
        (list 'caddr caddr)
        (list 'cdadr cdadr)
        (list 'cddar cddar)
        (list 'cons cons)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list 'null? null?)
        ))

(define (primitive-procedure-names)
  (map car
       primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))

(define the-global-environment (setup-environment))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))

(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")
(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input string)
  (newline) (newline)
  (display string)
  (newline))

(define (announce-output string)
  (newline)
  (display string)
  (newline))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))
