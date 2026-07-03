#lang sicp


(define (eval expr env)
  (cond
    [(self-evaluating? expr) expr]
    [(variable? expr) (lookup-variable-value expr env)]
    [(quoted? expr) (text-of-quotation expr)]
    [(assignment? expr) (eval-assignment expr env)]
    [(definition? expr) (eval-definition expr env)]
    [(lambda? expr)
     (make-procedure (lambda-parameters expr)
                     (scan-out-defines (lambda-body expr)) ; Exercise 4.16
                     env)]
    [(begin? expr)
     (eval-sequence (begin-actions expr) env)]
    [(if? expr) (eval-if expr env)]
    [(cond? expr) (eval (cond->if expr) env)]
    [(and? expr) (eval-and expr env)] ; and & or: Exercise 4.4
    [(or? expr) (eval-or expr env)]
    [(let? expr) (eval (let->combination expr) env)] ; let: Exercise 4.6
    [(let*? expr) (eval (let*->nested-lets expr) env)] ; let*: Exercise 4.7
    [(letrec? expr) (eval (letrec->let expr) env)] ; letrec: Exercise 4.20
    [(application? expr)
     (my-apply (eval (operator expr) env)
               (list-of-values (operands expr) env))]
    [else (error "Unknown expression type -- EVAL" expr)]))

(define (my-apply procedure arguments)
  (cond
    [(primitive-procedure? procedure)
     (apply-primitive-procedure procedure arguments)]
    [(compound-procedure? procedure)
     (eval-sequence
      (procedure-body procedure)
      (extend-environment
       (procedure-parameters procedure)
       arguments
       (procedure-environment procedure)))]
    [else (error "Unknown procedure type -- APPLY" (list procedure arguments))]))
(define (list-of-values exprs env)
  (if (no-operands? exprs)
      '()
      (cons (eval (first-operand exprs) env)
            (list-of-values (rest-operands exprs) env))))

(define (eval-if expr env)
  (if (true? (eval (if-predicate expr) env))
      (eval (if-consequent expr) env)
      (eval (if-alternative expr) env)))

(define (eval-sequence exprs env)
  (cond [(last-expr? exprs) (eval (first-expr exprs) env)]
        [else (eval (first-expr exprs) env)
              (eval-sequence (rest-exprs exprs) env)]))

(define (eval-assignment expr env)
  (set-variable-value! (assignment-variable expr)
                 (eval (assignment-value expr) env)
                 env)
  'ok)

(define (eval-definition expr env)
  (define-variable! (definition-variable expr)
                    (eval (definition-value expr) env)
                    env)
  'ok)
(define (self-evaluating? expr)
  (cond [(number? expr) true]
        [(string? expr) true]
        [else false]))

(define (variable? expr) (symbol? expr))

;; quote
(define (quoted? expr)
  (tagged-list? expr 'quote))
(define (text-of-quotation expr) (cadr expr))

(define (tagged-list? expr tag)
  (if (pair? expr)
      (eq? (car expr) tag)
      false))

;; assignment
(define (make-assignment var val)
  (list 'set! var val))
(define (assignment? expr)
  (tagged-list? expr 'set!))
(define (assignment-variable expr) (cadr expr))
(define (assignment-value expr) (caddr expr))

;; definition
(define (definition? expr)
  (tagged-list? expr 'define))
(define (definition-variable expr)
  (if (symbol? (cadr expr))
      (cadr expr)           ; (define <var> <value>)
      (caadr expr)))        ; (define (function_name arg...) <value>)
(define (definition-value expr)
  (if (symbol? (cadr expr))
      (caddr expr)
      (make-lambda (cdadr expr)
                   (cddr expr))))
; lambda
(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))
(define (lambda? expr) (tagged-list? expr 'lambda))
(define lambda-parameters cadr)
(define lambda-body cddr)

;; if
(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))
(define (if? expr) (tagged-list? expr 'if))
(define if-predicate cadr)
(define if-consequent caddr)
(define (if-alternative expr)
  (if (not (null? (cdddr expr)))
      (cadddr expr)
      false))

;; begin
(define (begin? expr) (tagged-list? expr 'begin))
(define (begin-actions expr) (cdr expr))
(define (last-expr? seq) (null? (cdr seq)))
(define first-expr car)
(define rest-exprs cdr)

(define (sequence->expr seq)
  (cond [(null? seq) seq]
        [(last-expr? seq) (first-expr seq)]
        [else (make-begin seq)]))
(define (make-begin seq) (cons 'begin seq))

;; apply
(define (application? expr) (pair? expr))
(define operator car)
(define operands cdr)
(define (no-operands? ops) (null? ops))
(define first-operand car)
(define rest-operands cdr)

;; cond
(define (cond? expr) (tagged-list? expr 'cond))
(define cond-clauses cdr)
(define (cond-predicate clause) (car clause))
(define (cond-actions clause) (cdr clause))
(define (cond-else-clause? clause) (eq? (cond-predicate clause) 'else))

(define (cond->if expr)
  (expand-clauses (cond-clauses expr)))

(define (expand-clauses clauses)
  (if (null? clauses)
      false              ; clause else
      (let ([first (car clauses)] [rest (cdr clauses)])
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->expr (cond-actions first))
                (error "ELSE clause is not last -- COND->IF" clauses))
            (make-if (cond-predicate first)
                     (sequence->expr (cond-actions first))
                     (expand-clauses rest))))))
(define (and? expr) (tagged-list? expr 'and))
(define (eval-and expr env)
  (define (iter seq)
    (let ([curr (eval (first-expr seq) env)])
      (if (not curr) false
          (if (last-expr? seq)
              curr
              (iter (rest-exprs seq))))))
  (if (null? (cdr expr)) true
      (iter (cdr expr))))

(define (or? expr) (tagged-list? expr 'or))
(define (eval-or expr env)
  (define (iter seq)
    (let ([curr (eval (first-expr seq) env)])
      (if curr true
          (if (last-expr? seq)
              curr
              (iter (rest-exprs seq))))))
  (if (null? (cdr expr)) false
      (iter (cdr expr))))
(define (make-application proc exprs)
  (cons proc exprs))

(define (make-let bindings body)
  (list 'let bindings body))
(define (let? expr) (tagged-list? expr 'let))
(define let-bindings cadr)
(define let-body cddr)
(define (binding? expr) (and (pair? expr) (pair? (cdr expr)) (null? (cddr expr))
                             (variable? (car expr))))
(define bindings-first car)
(define bindings-rest cdr)
(define binding-variable car)
(define binding-value cadr)

(define (let->combination expr)
  (define (iter bindings variables exprs)
    (if (null? bindings) (cons variables exprs)
        (let ([first (bindings-first bindings)]
              [rest (bindings-rest bindings)])
          (if (binding? first)
              (iter rest
                    (cons (binding-variable first) variables) ; note that it reverse the order
                    (cons (binding-value first) exprs))
              (error "Binding form illegal -- LET" first)))))

  (let ([parameters-expressions (iter (let-bindings expr) '() '())])
    (make-application (make-lambda (car parameters-expressions)
                                   (list (sequence->expr (let-body expr))))
                      (cdr parameters-expressions))))
(define (let*? expr) (tagged-list? expr 'let*))
(define (let*->nested-lets expr)
  (let ([bindings (let-bindings expr)])
    (if (or (null? bindings) (last-expr? bindings))
        expr
        (make-let (bindings-first bindings)
                  (let*->nested-lets (make-let (bindings-rest bindings)
                                               (let-body expr)))))))
(define (true? x)
  (not (eq? x false)))
(define (false? x)
  (eq? x false))
(define (make-procedure parameters body env)
  (list 'procedure parameters body env))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define procedure-parameters cadr)
(define procedure-body caddr)
(define procedure-environment cadddr)
(define the-empty-environment '())
(define (enclosing-environment envs) (cdr envs))
(define (first-frame envs) (car envs))

(define (zip2 xs ys)
  (map list xs ys))

(define (make-frame-by-bindings bindings) bindings) ; a frame is bindings
(define (make-frame vars vals) (zip2 vars vals))
(define (make-binding var val) (list var val))
;; (define binding-variable car) ; they are defined above
;; (define binding-value cadr)
(define (bind-new-value! binding val)
  (set-cdr! binding (list val)))

;; this procedure is the same with example in book
(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied -- EXTEND-ENVIRONMENT" vars vals)
          (error "Too few arguments supplied -- EXTEND-ENVIRONMENT" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (if (eq? env the-empty-environment)
        (error "Unbound variable:" var)
        (let ([record (assv var (first-frame env))])
          (if record
              (binding-value record)
              (env-loop (enclosing-environment env))))))
  (env-loop env))
(define (set-variable-value! var val env)
  (define (env-loop env)
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ([record (assv var (first-frame env))])
          (if record
              (bind-new-value! record val)
              (env-loop (enclosing-environment env))))))
  (env-loop env))
(define (define-variable! var val env)
  (let* ([frame (first-frame env)]
         [record (assv var frame)])
    (if record
        (bind-new-value! record val)
        (set-car! env (cons (make-binding var val) frame)))))
(define (setup-environment)
  (let ([initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)])
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

(define (primitive-procedure? expr)
  (tagged-list? expr 'primitive))
(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list
   (list 'car car) (list 'cdr cdr)
   (list 'cons cons) (list 'null? null?)
   (list 'list list) (list 'pair? pair?)
   (list '+ +) (list '- -) (list '* *) (list '/ /)
   (list '= =) (list '< <) (list '> >)
   (list 'display display) (list 'newline newline) ; Exercise 4.30
   (list 'eq? eq?) ; Exercise 4.34
   ))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))

(define apply-in-underlying-scheme apply)
(define (unassigned-bindings vars)
  (map (lambda (var) (make-binding var ''*unassigned*)) vars))

(define (scan-out-defines proc-body)
  (define (reversed lst)
    (define (iter xs acc)
      (if (null? xs) acc
          (iter (cdr xs) (cons (car xs) acc))))
    (iter lst '()))
  (define (iter rests acc-v acc-e acc-b)
    ;; in r5rs, the last expr of a procedure body should not be a definition;
    ;; but I choose to return a '<void> simply
    (cond [(null? rests) (list (reversed acc-v) (reversed acc-e) ''<void>)]
          [(and (last-expr? rests)
                (not (definition? (first-expr rests))))
           (list (reversed acc-v) (reversed acc-e)
                 (sequence->expr (reversed (cons (first-expr rests) acc-b))))]
          [(definition? (first-expr rests))
           (let ([def (first-expr rests)])
             (iter (cdr rests)
                   (cons (definition-variable def) acc-v)
                   (cons (definition-value def) acc-e)
                   acc-b))]
          [else (iter (cdr rests) acc-v acc-e
                      (cons (first-expr rests) acc-b))]))
  (let ([vars-vals-expr (iter proc-body '() '() '())])
    (let ([vars (car vars-vals-expr)]
          [vals (cadr vars-vals-expr)]
          [expr (caddr vars-vals-expr)])
      (if (null? vars) proc-body
          (list (make-let (unassigned-bindings vars)
                          (sequence->expr
                           (append (map (lambda (var val)
                                          (make-assignment var val)) vars vals)
                                   (list expr)))))))))
(define (unzip2 pairs)
  (define (fold-left f acc lst)
    (if (null? lst) acc
        (fold-left f (f acc (car lst)) (cdr lst))))
  
  (define (fold-right f lst acc)
    (if (null? lst) acc
        (f (car lst) (fold-right f (cdr lst) acc))))
  (define first car)
  (define second cadr)
  (fold-right (lambda (pair acc)
                (cons (cons (first pair) (car acc))
                      (cons (second pair) (cdr acc))))
              pairs (cons nil nil)))
(define (bindings-variables-values bindings)
  (unzip2 bindings))

(define (letrec? expr)
  (tagged-list? expr 'letrec))
(define letrec-bindings cadr)
(define letrec-body cddr)
(define (letrec->let expr)
  (let ([vars-vals (bindings-variables-values (letrec-bindings expr))])
    (make-let (unassigned-bindings (car vars-vals))
              (sequence->expr (append (map (lambda (var val) (make-assignment var val)) (car vars-vals) (cdr vars-vals))
                                      (letrec-body expr))))))
(define (actual-value expr env)
  (force-it (eval-lazy expr env)))

(define (eval-lazy expr env)
  (cond
    [(self-evaluating? expr) expr]
    [(variable? expr) (lookup-variable-value expr env)]
    [(quoted? expr) (text-of-quotation expr)]
    [(assignment? expr) (eval-assignment expr env)]
    [(definition? expr) (eval-definition expr env)]
    [(lambda? expr)
     (make-procedure (lambda-parameters expr)
                     (scan-out-defines (lambda-body expr)) ; Exercise 4.16
                     env)]
    [(begin? expr)
     (eval-sequence (begin-actions expr) env)]
    [(if? expr) (eval-if-lazy expr env)]
    [(cond? expr) (eval-lazy (cond->if expr) env)]
    [(and? expr) (eval-and expr env)] ; and & or: Exercise 4.4
    [(or? expr) (eval-or expr env)]
    [(let? expr) (eval-lazy (let->combination expr) env)] ; let: Exercise 4.6
    [(let*? expr) (eval-lazy (let*->nested-lets expr) env)] ; let*: Exercise 4.7
    [(letrec? expr) (eval-lazy (letrec->let expr) env)] ; letrec: Exercise 4.20
    [(application? expr)
     (apply-lazy (actual-value (operator expr) env) ;; CHANGED HERE
                 (operands expr)
                 env)]
    [else (error "Unknown expression type -- EVAL" expr)]))

(define (apply-lazy procedure arguments env)
  (cond
    [(primitive-procedure? procedure)
     (apply-primitive-procedure
      procedure
      (list-of-arg-values arguments env))]
    [(compound-procedure? procedure)
     (eval-sequence
      (procedure-body procedure)
      (extend-environment
       (procedure-parameters procedure)
       (list-of-delayed-args arguments env)
       (procedure-environment procedure)))]
    [else (error "Unknown procedure type -- APPLY" (list procedure arguments))]))

(define (list-of-arg-values exprs env)
  (if (no-operands? exprs) '()
      (cons (actual-value (first-operand exprs) env)
            (list-of-arg-values (rest-operands exprs) env))))

(define (list-of-delayed-args exprs env)
  (if (no-operands? exprs) '()
      (cons (delay-it (first-operand exprs) env)
            (list-of-delayed-args (rest-operands exprs) env))))

(define (eval-if-lazy expr env)
  (if (true? (actual-value (if-predicate expr) env))
      (eval-lazy (if-consequent expr) env)
      (eval-lazy (if-alternative expr) env)))
(define (force-it-exp obj)
  (if (thunk? obj)
      (actual-value (thunk-expr obj) (thunk-env obj))
      obj))

(define (delay-it expr env) (make-thunk expr env))

(define (make-thunk expr env)
  (list 'thunk expr env))
(define (thunk? obj)
  (tagged-list? obj 'thunk))
(define thunk-expr cadr)
(define thunk-env caddr)

(define (evaluated-thunk? obj)
  (tagged-list? obj 'evaluated-thunk))
(define (thunk-value evaluated-thunk) (cadr evaluated-thunk))

(define (force-it obj)
  (cond [(thunk? obj)
         (let ([result (actual-value (thunk-expr obj) (thunk-env obj))])
           (set-car! obj 'evaluated-thunk)
           (set-car! (cdr obj) result)
           (set-cdr! (cdr obj) '())
           result)]
        [(evaluated-thunk? obj) (thunk-value obj)]
        [else obj]))
(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval output:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ([input (read)])
    (let ([output (eval input the-global-environment)])
      (announce-output output-prompt)
      (user-print output))
    (driver-loop)))

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))
(define (announce-output string)
  (newline) (display string) (newline))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))
(set! eval eval-lazy)
(define the-global-environment (setup-environment))
(define (eval-lazy-repl-scope)
  (define input-prompt ";;; L-Eval input:")
  (define output-prompt ";;; L-Eval output:")
  
  (define (driver-loop)
    (prompt-for-input input-prompt)
    (let* ([input (read)]
           [output (actual-value input the-global-environment)])
      (announce-output output-prompt)
      (user-print output))
    (driver-loop))
  (driver-loop)
)
(eval-lazy-repl-scope)
