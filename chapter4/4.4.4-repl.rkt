#lang sicp


(#%require (only racket make-hash hash-set! hash-ref))

(define (make-two-dimention-key k1 k2)
  (list k1 '*hash-dimention-divisor* k2))

(define the-global-table (make-hash))

(define (put k1 k2 v)
  (hash-set! the-global-table (make-two-dimention-key k1 k2) v))
(define (get k1 k2)
  (hash-ref the-global-table (make-two-dimention-key k1 k2) false))

(define (get-or k1 k2 alternative)
  (hash-ref the-global-table (make-two-dimention-key k1 k2) alternative))
(define (instantiate expr frame unbound-var-handler)
  (define (copy expr)
    (cond [(var? expr)
           (let ([binding (binding-in-frame expr frame)])
             (if binding
                 (copy (binding-value binding))
                 (unbound-var-handler expr frame)))]
          [(pair? expr)
           (cons (copy (car expr)) (copy (cdr expr)))]
          [else expr]))
  (copy expr))
(define (qeval query frame-stream)
  (let ([qproc (get (type query) 'qeval)])
    (if qproc
        (qproc (contents query) frame-stream)
        (simple-query query frame-stream))))

(define (simple-query query-pattern frame-stream)
  (stream-flatmap
   (lambda (frame)
     (stream-append-delayed
      (find-assertions query-pattern frame)
      (delay (apply-rules query-pattern frame))))
   frame-stream))
(define (conjoin conjuncts frame-stream)
  (if (empty-conjunction? conjuncts)
      frame-stream
      (conjoin (rest-conjuncts conjuncts)
               (qeval (first-conjunct conjuncts)
                      frame-stream))))

(put 'and 'qeval conjoin)
(define (disjoin disjuncts frame-stream)
  (if (empty-disjunction? disjuncts)
      the-empty-stream
      (interleave-delayed
       (qeval (first-disjunct disjuncts) frame-stream)
       (delay (disjoin (rest-disjuncts disjuncts)
                       frame-stream)))))

(put 'or 'qeval disjoin)
(define (negate operands frame-stream)
  (stream-flatmap
   (lambda (frame)
     (if (stream-null? (qeval (negated-query operands)
                              (singleton-stream frame)))
         (singleton-stream frame)
         the-empty-stream))
   frame-stream))

(put 'not 'qeval negate)
(define (lisp-value call frame-stream)
  (stream-flatmap
   (lambda (frame)
     (if (execute
          (instantiate
           call
           frame
           (lambda (v f)
             (error "Unknown pat var -- LISP-VALUE" v))))
          (singleton-stream frame)
          the-empty-stream))
   frame-stream))

(put 'lisp-value 'qeval lisp-value)
(define user-initial-environment (scheme-report-environment 5))

(define (execute expr)
  (apply (eval (predicate expr) user-initial-environment)
         (args expr)))
(define (always-true ignore frame-stream) frame-stream)

(put 'always-true 'qeval always-true)
(define (find-assertions pattern frame)
  (stream-flatmap
   (lambda (datum)
     (check-an-assertion datum pattern frame))
   (fetch-assertions pattern frame)))

(define (check-an-assertion assertion query-pat query-frame)
  (let ([match-result
         (pattern-match query-pat assertion query-frame)])
    (if (eq? match-result 'failed)
        the-empty-stream
        (singleton-stream match-result))))
(define (pattern-match pat dat frame)
  (cond [(eq? frame 'failed) 'failed]
        [(equal? pat dat) frame]
        [(var? pat) (extend-if-consist pat dat frame)]
        [(and (pair? pat) (pair? dat))
         (pattern-match (cdr pat)
                        (cdr dat)
                        (pattern-match (car pat)
                                       (car dat)
                                       frame))]
        [else 'failed]))

(define (extend-if-consist var dat frame)
  (let ([binding (binding-in-frame var frame)])
    (if binding
        (pattern-match (binding-value binding) dat frame)
        (extend var dat frame))))
(define (apply-rules pattern frame)
  (stream-flatmap (lambda (rule)
                    (apply-a-rule rule pattern frame))
                  (fetch-rules pattern frame)))

(define (apply-a-rule rule query-pattern query-frame)
  (let ([clean-rule (rename-variables-in rule)])
    (let ([unify-result
           (unify-match query-pattern
                        (conclusion clean-rule)
                        query-frame)])
      (if (eq? unify-result 'failed)
          the-empty-stream
          (qeval (rule-body clean-rule)
                 (singleton-stream unify-result))))))
(define (rename-variables-in rule)
  (let ([rule-application-id (new-rule-application-id)])
    (define (tree-walk expr)
      (cond [(var? expr)
             (make-new-variable expr rule-application-id)]
            [(pair? expr)
             (cons (tree-walk (car expr))
                   (tree-walk (cdr expr)))]
            [else expr]))
    (tree-walk rule)))
(define (unify-match p1 p2 frame)
  (cond [(eq? frame 'failed) 'failed]
        [(equal? p1 p2) frame]
        [(var? p1) (extend-if-possible p1 p2 frame)]
        [(var? p2) (extend-if-possible p2 p1 frame)]
        [(and (pair? p1) (pair? p2))
         (unify-match (cdr p1)
                      (cdr p2)
                      (unify-match (car p1)
                                   (car p2)
                                   frame))]
        [else 'failed]))

(define (extend-if-possible var val frame)
  (let ([binding (binding-in-frame var frame)])
    (cond [binding
           (unify-match
            (binding-value binding) val frame)]
          [(var? val)
           (let ([binding (binding-in-frame val frame)])
             (if binding
                 (unify-match
                  var (binding-value binding) frame)
                 (extend var val frame)))]
          [(depends-on? val var frame) 'failed]
          [else (extend var val frame)])))

(define (depends-on? expr var frame)
  (define (tree-walk e)
    (cond [(var? e)
           (if (equal? var e)
               true
               (let ([b (binding-in-frame e frame)])
                 (if b
                     (tree-walk (binding-value b))
                     false)))]
          [(pair? e)
           (or (tree-walk (car e))
               (tree-walk (cdr e)))]
          [else false]))
  (tree-walk expr))
(define THE-ASSERTIONS the-empty-stream)
(define (get-all-assertions) THE-ASSERTIONS)

(define (fetch-assertions pattern frame)
  (if (use-index? pattern)
      (get-indexed-assertions pattern)
      (get-all-assertions)))

(define (get-indexed-assertions pattern)
  (get-stream (index-key-of pattern) 'assertion-stream))

(define (get-stream key1 key2)
  (get-or key1 key2 the-empty-stream))
(define THE-RULES the-empty-stream)
(define (get-all-rules) THE-RULES)

(define (fetch-rules pattern frame)
  (if (use-index? pattern)
      (get-indexed-rules pattern)
      (get-all-rules)))

(define (get-indexed-rules pattern)
  (stream-append
   (get-stream (index-key-of pattern) 'rule-stream)
   (get-stream '? 'rule-stream)))
(define (add-rule-or-assertion! assertion)
  (if (rule? assertion)
      (add-rule! assertion)
      (add-assertion! assertion)))

(define (add-assertion! assertion)
  (store-assertion-in-index assertion)
  (let ([old-assertions THE-ASSERTIONS])
    (set! THE-ASSERTIONS (cons-stream assertion old-assertions))
    'ok))

(define (add-rule! rule)
  (store-rule-in-index rule)
  (let ([old-rules THE-RULES])
    (set! THE-RULES (cons-stream rule old-rules))
    'ok))
(define (store-assertion-in-index assertion)
  (if (indexable? assertion)
      (let ([key (index-key-of assertion)])
        (let ([current-assertion-stream
               (get-stream key 'assertion-stream)])
          (put key
               'assertion-stream
               (cons-stream assertion
                            current-assertion-stream))))))

(define (store-rule-in-index rule)
  (let ([pattern (conclusion rule)])
    (if (indexable? pattern)
        (let ([key (index-key-of pattern)])
          (let ([current-rule-stream
                 (get-stream key 'rule-stream)])
            (put key
                 'rule-stream
                 (cons-stream rule
                              current-rule-stream)))))))

(define (indexable? pat)
  (or (constant-symbol? (car pat))
      (var? (car pat))))

(define (index-key-of pat)
  (let ([key (car pat)])
    (if (var? key) '? key)))

(define (use-index? pat)
  (constant-symbol? (car pat)))
(define (type expr)
  (if (pair? expr)
      (car expr)
      (error "Unknown expression TYPE" expr)))

(define (contents expr)
  (if (pair? expr)
      (cdr expr)
      (error "Unknown expression CONTENTS" expr)))

(define (assertion-to-be-added? expr)
  (eq? (type expr) 'assert!))

(define (add-assertion-body expr)
  (car (contents expr)))
(define empty-conjunction? null?)
(define first-conjunct car)
(define rest-conjuncts cdr)

(define empty-disjunction? null?)
(define first-disjunct car)
(define rest-disjuncts cdr)

(define (negated-query expr) (car expr))
(define (predicate expr) (car expr))
(define (args expr) (cdr expr))

(define (rule? statement)
  (tagged-list? statement 'rule))
(define (conclusion rule) (cadr rule))
(define (rule-body rule)
  (if (null? (cddr rule))
      '(always-true)
      (caddr rule)))
(define (query-syntax-process expr)
  (map-over-symbols expand-question-mark expr))

(define (map-over-symbols proc expr)
  (cond [(pair? expr)
         (cons (map-over-symbols proc (car expr))
               (map-over-symbols proc (cdr expr)))]
        [(symbol? expr) (proc expr)]
        [else expr]))

(define (expand-question-mark symbol)
  (let ([chars (symbol->string symbol)])
    (if (string=? (substring chars 0 1) "?")
        (list '?
              (string->symbol
               (substring chars 1 (string-length chars))))
        symbol)))

(define (contract-question-mark variable)
  (string->symbol
   (string-append "?"
                  (if (number? (cadr variable))
                      (string-append (symbol->string (caddr variable))
                                     "-"
                                     (number->string (cadr variable)))
                      (symbol->string (cadr variable))))))
(define (var? expr)
  (tagged-list? expr '?))

(define (constant-symbol? expr) (symbol? expr))

(define (make-binding variable value)
  (cons variable value))
(define binding-variable car)
(define binding-value cdr)

(define (binding-in-frame variable name)
  (assoc variable name))

(define (extend variable value frame)
  (cons (make-binding variable value) frame))
(define rule-counter 0)
(define (new-rule-application-id)
  (set! rule-counter (+ 1 rule-counter))
  rule-counter)
(define (make-new-variable var rule-application-id)
  (cons '? (cons rule-application-id (cdr var))))
(define (stream-singleton? s)
  (cond [(stream-null? s) false]
        [(stream-null? (stream-cdr s)) true]
        [else false]))
(define (list-singleton? l)
  (cond [(null? l) false]
        [(null? (cdr l)) true]
        [else false]))

(define empty-unique-query? null?)
(define unique-query car)
(define unique-query-singleton? list-singleton?)

(define (uniquely-asserted queries frame-stream)
  (define (singleton-or-empty s)
    (if (stream-singleton? s) s
        the-empty-stream))
  (cond [(empty-unique-query? queries) frame-stream]
        [(unique-query-singleton? queries)
          (stream-flatmap
           (lambda (frame)
             (singleton-or-empty
              (qeval (unique-query queries)
                     (singleton-stream frame))))
           frame-stream)]
        [else
         (error "Multiple queries in UNIQUE query" queries)]))

(put 'unique 'qeval uniquely-asserted)
(define (conjoin2 conjuncts frame-stream)
  (cond [(empty-conjunction? conjuncts)
         frame-stream]
        [(empty-conjunction? (rest-conjuncts conjuncts))
         (qeval (first-conjunct conjuncts) frame-stream)]
        [else
         (let ([first (first-conjunct conjuncts)]
               [second (first-conjunct (rest-conjuncts conjuncts))]
               [rest (rest-conjuncts (rest-conjuncts conjuncts))])
           ; or use `conjoin2`
           (conjoin rest
                    (combine-frame-streams
                     (qeval first frame-stream)
                     (qeval second frame-stream))))]))

(define (combine-frame-streams xs ys)
  (stream-filter
   (lambda (frame) (not (eq? frame 'failed-combine)))
   (stream-flatmap (lambda (y)
                     (stream-map (lambda (x)
                                   (combine-frame x y))
                                 xs))
                   ys)))

(define (binding? expr)
  (and (pair? expr)
       (var? (binding-variable expr))))

(define (frame-bindings expr)
  (define (iter subexpr)
    (cond [(null? subexpr) subexpr]
          [(binding? (car subexpr))
           (cons (car subexpr)
                 (iter (cdr subexpr)))]
          [else (iter (cdr subexpr))]))
  (iter expr))

(define bindings-first car)
(define bindings-rest cdr)

; combine if the value of according var equals
(define (combine-frame f1 f2)
  (define (do-combine f1 f2) f2)
  (define (iter bindings)
    (cond [(eq? bindings 'failed-combine) 'failed-combine]
          [(null? bindings) (do-combine f1 f2)]
          [else
           (let ([binding1 (bindings-first bindings)])
             (let ([binding2 (binding-in-frame (binding-variable binding1) f2)])
               (if (and binding2
                        (equal? (binding-value binding1)
                                (binding-value binding2)))
                   (iter (bindings-rest bindings))
                   'failed-combine)))]))
  (iter (frame-bindings f1)))

(put 'and2 'qeval conjoin2)
(define (stream-append-delayed s1 delayed-s2)
  (if (stream-null? s1)
      (force delayed-s2)
      (cons-stream
       (stream-car s1)
       (stream-append-delayed (force delayed-s2)
                              (delay (stream-cdr s1))))))

(define (interleave-delayed s1 delayed-s2)
  (if (stream-null? s1)
      (force delayed-s2)
      (cons-stream
       (stream-car s1)
       (interleave-delayed (force delayed-s2)
                           (delay (stream-cdr s1))))))

(define (stream-flatmap proc s)
  (flatten-stream (stream-map proc s)))

(define (flatten-stream sss)
  (if (stream-null? sss)
      the-empty-stream
      (interleave-delayed
       (stream-car sss)
       (delay (flatten-stream (stream-cdr sss))))))

(define (singleton-stream x)
  (cons-stream x the-empty-stream))
(define stream-car car)
(define (stream-cdr ss) (force (cdr ss)))

(define (list->stream lst)
  (if (null? lst) the-empty-stream
      (cons-stream (car lst)
                   (list->stream (cdr lst)))))
(define (stream . items)
  (list->stream items))

(define (stream-map f . sss)
  (define (fold-left f acc lst)
    (if (null? lst) acc
        (fold-left f (f acc (car lst)) (cdr lst))))
  
  (define (fold-right f lst acc)
    (if (null? lst) acc
        (f (car lst) (fold-right f (cdr lst) acc))))
  (if (stream-null? (car sss))
      the-empty-stream
      (cons-stream (apply f (map stream-car sss))
                   (apply stream-map (cons f (map stream-cdr sss))))))

(define (stream-filter f ss)
  (cond [(stream-null? ss) the-empty-stream]
        [(f (stream-car ss))
         (cons-stream (stream-car ss)
                      (stream-filter f (stream-cdr ss)))]
        [else (stream-filter f (stream-cdr ss))]))
(define (stream-take ss n)
  (cond [(stream-null? ss) '()]
        [(<= n 0) '()]
        [else (cons (stream-car ss) (stream-take (stream-cdr ss) (- n 1)))]))

(define (stream-append xs ys)
  (cond [(stream-null? xs) ys]
        [(stream-null? ys) xs]
        [else
         (cons-stream (stream-car xs)
                      (stream-append (stream-cdr xs)
                                     ys))]))

(define (stream-foreach f ss)
  (if (not (stream-null? ss))
      (begin (f (stream-car ss))
             (stream-foreach f (stream-cdr ss)))))

(define (display-stream ss)
  (stream-foreach (lambda (x) (display x) (newline)) ss))

(define ones (cons-stream 1 ones))
(define integers (cons-stream 1 (add-streams ones integers)))

(define (add-streams . sss)
  (apply stream-map (cons + sss)))

(define (integers-start-from n)
  (define (iter ss)
    (if (= n (stream-car ss)) ss
        (iter (stream-cdr ss))))
  (iter integers))

(define (divisible? x n)
  (= (remainder x n) 0))

(define (sieve ss)
  (cons-stream (stream-car ss)
               (sieve (stream-filter
                       (lambda (x) (not (divisible? x (stream-car ss))))
                       (stream-cdr ss)))))
(define primes (sieve (integers-start-from 2)))
(define (tagged-list? expr tag)
  (if (pair? expr) (eq? (car expr) tag)
      false))

(define (load-entries-by f exprs)
  (map (lambda (assertion-expr)
         (add-rule-or-assertion!
          (add-assertion-body
           (query-syntax-process
            (f assertion-expr)))))
       exprs))

(define (load-plain-database exprs)
  (define (format-result res)
    (define (fold-left f acc lst)
      (if (null? lst) acc
          (fold-left f (f acc (car lst)) (cdr lst))))
    
    (define (fold-right f lst acc)
      (if (null? lst) acc
          (f (car lst) (fold-right f (cdr lst) acc))))
    (let ([err (fold-right (lambda (e acc) (if (eq? e 'ok) acc
                                               (cons e acc)))
                           res '())])
      (if (null? err) 'ok err)))
  (format-result
   (load-entries-by (lambda (e) (list 'assertion e)) exprs)))

(define (qeval-stream expr)
  (let ([q (query-syntax-process expr)])
    (stream-map
      (lambda (frame)
        (instantiate q
                     frame
                     (lambda (v f)
                       (contract-question-mark v))))
      (qeval q (singleton-stream '())))))

(define (qeval-display expr)
  (display-stream (qeval-stream expr)))

(define (qeval-display-formatted expr)
  (display "$ ") (display expr) (newline)
  (qeval-display expr))
(define database-company
  (list
   '(address (Bitdiddle Ben) (Slumerville (Ridge Road) 10))
   '(job (Bitdiddle Ben) (computer wizard))
   '(salary (Bitdiddle Ben) 60000)

   '(address (Hacker Alyssa P) (Cambridge (Mass Ave) 78))
   '(job (Hacker Alyssa P) (computer programmer))
   '(salary (Hacker Alyssa P) 40000)
   '(supervisor (Hacker Alyssa P) (Bitdiddle Ben))
   '(address (Fect Cy D) (Cambridge (Ames Street) 3))
   '(job (Fect Cy D) (computer programmer))
   '(salary (Fect Cy D) 35000)
   '(supervisor (Fect Cy D) (Bitdiddle Ben))
   '(address (Tweakit Lem E) (Boston (Bay State Road) 22))
   '(job (Tweakit Lem E) (computer technician))
   '(salary (Tweakit Lem E) 25000)
   '(supervisor (Tweakit Lem E) (Bitdiddle Ben))

   '(address (Reasoner Louis) (Slumerville (Pine Tree Road) 80))
   '(job (Reasoner Louis) (computer programmer trainee))
   '(salary (Reasoner Louis) 30000)
   '(supervisor (Reasoner Louis) (Hacker Alyssa P))

   '(supervisor (Bitdiddle Ben) (Warbucks Oliver))
   '(address (Warbucks Oliver) (Swellesley (Top Heap Road)))
   '(job (Warbucks Oliver) (administration big wheel))
   '(salary (Warbucks Oliver) 150000)

   '(address (Scrooge Eben) (Weston (Shady Lane) 10))
   '(job (Scrooge Eben) (accounting chief accountant))
   '(salary (Scrooge Eben) 75000)
   '(supervisor (Scrooge Eben) (Warbucks Oliver))
   '(address (Cratchet Robert) (Allston (N Harvard Street) 16))
   '(job (Cratchet Robert) (accounting scrivener))
   '(salary (Cratchet Robert) 18000)
   '(supervisor (Cratchet Robert) (Scrooge Eben))

   '(address (Aull DeWitt) (Slumerville (Onion Square) 5))
   '(job (Aull DeWitt) (administration secretary))
   '(salary (Aull DeWitt) 25000)
   '(supervisor (Aull DeWitt) (Warbucks Oliver))

   '(can-do-job (computer wizard) (computer programmer))
   '(can-do-job (computer wizard) (computer technician))

   '(can-do-job (computer programmer)
                (computer programmer trainee))

   '(can-do-job (administration secretary)
                (administration big wheel))
   ))
(load-plain-database database-company)
(define input-prompt ";;; Query input:")
(define output-prompt ";;; Query results:")

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))

(define (query-driver-loop)
  (prompt-for-input input-prompt)
  (let ([q (query-syntax-process (read))])
    (cond [(assertion-to-be-added? q)
           (add-rule-or-assertion! (add-assertion-body q))
           (newline)
           (display "Assertion added to data base.")
           (query-driver-loop)]
          [else
           (newline)
           (display output-prompt)
           (display-stream
            (stream-map
             (lambda (frame)
               (instantiate q
                            frame
                            (lambda (v f)
                              (contract-question-mark v))))
             (qeval q (singleton-stream '()))))
           (query-driver-loop)])))
(query-driver-loop)
