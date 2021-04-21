#lang racket #| * CSC324 Fall 2019: Assignment 1 * |#
#|
Module: dubdub
Description: Assignment 1: A More Featureful Interpreter
Copyright: (c)University of Toronto, University of Toronto Mississauga 
               CSC324 Principles of Programming Languages, Fall 2019

The assignment handout can be found at

    https://www.cs.toronto.edu/~lczhang/324/files/a1.pdf

Please see the assignment guidelines at 

    https://www.cs.toronto.edu/~lczhang/324/homework.html
|#

(provide run-interpreter)

(require "dubdub_errors.rkt")


;-----------------------------------------------------------------------------------------
; Main functions (skeleton provided in starter code)
;-----------------------------------------------------------------------------------------
#|
(run-interpreter prog) -> any
  prog: datum?
    A syntactically-valid Dubdub program.

  Evaluates the Dubdub program and returns its value, or raises an error if the program is
  not semantically valid.
|#

(define (run-interpreter prog)
  (run-helper prog (hash))
  )

;-----------------------------------------------------------------------------------------
; Helpers: Builtins and closures
;-----------------------------------------------------------------------------------------

#|
(plus-helper lst env) -> integer
    lst: datum?
    List of numbers that need to be added together
    env: hash?
    The environment with which to evaluate the expression.
    A syntactically-valid Dubdub expression.
  Returns an integer of all the added integers in a list
|#
(define (plus-helper lst env)
  (cond
    [(null? lst) 0] ;Exit the loop
    [else (let ([fn (first lst)] [rn (rest lst)])
            (apply
             + (cond
                 [(number? fn) fn]
                 [(list? fn)
                  (cond
                    [(equal? (first fn) '+) (plus-helper (rest fn) env)]
                    [else (run-helper (list fn) env)]
                    )]
                 [else (run-helper (list fn) env)]
                 )
             (plus-helper rn env) '())
            )]))

; A hash mapping symbols for Dubdub builtin functions to their corresponding Racket value.
(define builtins
  (hash
   'any 'any
   'equal? equal?
   'integer? integer?
   'boolean? boolean?
   '< <
   ; Note: You'll almost certainly need to replace procedure? here to properly return #t
   ; when given your closure data structure at the end of Task 1!
   'procedure? procedure?
   ))

; Returns whether a given symbol refers to a builtin Dubdub function.
(define (builtin? identifier) (hash-has-key? builtins identifier))


#|
(defcon-checker id lst env orig) -> list/symbol
    id: symbol?
    The id of the define-contract
    lst: datum?
    List of subexpressions that need to be checked
    env: hash?
    The environment with which to evaluate the expression.
    orig: list?
    The original list of subexpressions
    A syntactically-valid Dubdub expression.
  Returns the orignial list of subexpressions or gives an error
|#
(define (defcon-checker id lst env orig)
  (cond
    [(null? lst) orig]  
    [(equal? (first lst) '->) (defcon-checker id (rest lst) env orig)]
    [(not (or (builtin? (first lst)) (hash-has-key? env (first lst)) (and (list? (first lst)) (equal? 'lambda (first (first lst))))
              (and (list? (first lst)) (equal? 'closure (first (first lst))))))
     'invalid-contract]
    [(and (not (builtin? (first lst))) (list? (first lst))(member 'lambda (first lst)))   ;For lambda only
     (cond
       [(< 1 (length (second (first lst)))) 'invalid-contract]
       [(not (builtin? (first (third (first lst))))) 'invalid-contract]
       [else (defcon-checker id (rest lst) env orig)]
       )]
    [(and (not (builtin? (first lst))) (list? (first lst))(member 'closure (first lst)))   ;For closure only
     (cond
       [(< 1 (length (second (second (first lst))))) 'invalid-contract]
       [(not (builtin? (first (third (second (first lst)))))) 'invalid-contract]
       [else (defcon-checker id (rest lst) env orig)]
       )]
    [(not (builtin? (first lst))) ;If not a builtin then is user-defined
     (print (first (third (hash-ref env (first lst)))))
     (cond
       [(equal? 'lambda (first (hash-ref env (first lst)))) ;Check if sub-expr is equal to lambda
        (cond
          [(<= 1 (length (second (hash-ref env (first lst))))) ;Check if lambda parameter is 1
           (print "invalid-contract")]
          [(not (builtin? (first (third (hash-ref env (first lst)))))) ;Check if in lambda the expr is valid
           (print "invalid-contract")]
          [else
           (defcon-checker id (rest lst) env orig)
           ])]
       [(equal? 'closure (first (hash-ref env (first lst)))) ;Check if sub-expr is equal to closure 
        (cond
          [(<= 1 (length (second (second (hash-ref env (first lst)))))) ;Check if closure parameter is 1
           (print "invalid-contract")]
          [(not (builtin? (first (third (second (hash-ref env (first lst))))))) ;Check if in closure the expr is valid
           (print "invalid-contract")]
          [else (defcon-checker id (rest lst) env orig)])])
  
     ][else (defcon-checker id (rest lst) env orig)])
  )

#|
(defcon-helper prog env lst orig) -> list/symbol
    prog: list?
    A expression that need to be checked against the define-contract
    lst: datum?
    List of subexpressions that need to be checked against
    env: hash?
    The environment with which to evaluate the expression.
    orig: list?
    The original expressions
    A syntactically-valid Dubdub expression.
  Returns the orignial list of subexpressions or gives an error
|#
(define (defcon-helper prog env lst orig)
  (cond
    [(null? lst) orig]
    [(equal? (first lst) '->) orig]
    [(not (run-helper (list (list (first lst) (run-helper (first prog) env))) env)) 'contract-violation]
    [else
     (defcon-helper (rest prog) env (rest lst) orig)]
    ))

(define (duplicate lst)
(cond
  [(null? lst) (list #f '())]
  [else
   (if (member (first lst) (rest lst)) (list #t (first lst)) (duplicate (rest lst)))]
  ))

#|
(run-helper prog env) -> any
  env: hash?
    The environment with which to evaluate the expression.
  prog: datum?
    A syntactically-valid Dubdub expression.

  Returest-progs the value of the Dubdub expression under the given environment.
|#
(define (run-helper prog env)
  (cond
    [(null? prog) prog]
    [(integer? prog) prog]
    [(boolean? prog) prog]
    [(hash-has-key? env prog) (hash-ref env prog)]
    [else (let ([first-prog (first prog)] [rest-prog (rest prog)]) ;All followings are list prog case
            (cond
              [(and (equal? (length prog) 1)(integer? first-prog)) first-prog] ;For the builtin "integer"
              [(boolean? first-prog) first-prog] ;For the builtin "boolean?"
              [(hash-has-key? env first-prog) (hash-ref env first-prog)] ;Check if the key is exist
              [(and (list? first-prog) (equal? (first first-prog) 'closure)) ;For the closure part
               (cond
                 [(equal? (length (second (first (second first-prog)))) (length (rest(second first-prog))))
                  (run-helper (list (third (first (second first-prog)))) (third first-prog))] 
                 [else
                   prog
                  ])]
              [(and (list? first-prog) (list? (first first-prog)) (member 'lambda (first first-prog))) ;For the lambda part
               (cond
                 [(let* ([dup (duplicate (second (first first-prog)))][chek (first dup)] [dup-id (second dup)])
                 (if chek (report-error 'duplicate-name dup-id) ;Check for duplicate names
                     (cond
                     [(< (length (second (first first-prog))) (length (rest first-prog)))
                  (report-error 'arity-mismatch first-prog (- (length first-prog) 1)  1)]
                 [(equal? (length (second (first first-prog))) (length (rest first-prog)))
                  (run-helper (list(list 'closure first-prog (run-helper (list (second (first first-prog)) (rest first-prog)) env)))
                              (run-helper (list (second (first first-prog)) (rest first-prog)) env))]
   
                 [(< (length (rest first-prog)) (length (second (first first-prog)))) ;Currying
                  (if (equal? (length rest-prog) 0)
                  (run-helper (list(list 'closure
                                         (list (append (list (first (first first-prog))) (list (list-tail (second (first first-prog)) (length (rest first-prog))))
                                                       (list (third (first first-prog)))))
                                         (run-helper (list (take (second (first first-prog)) (length (rest first-prog))) (rest first-prog)) env)))
                              (run-helper (list (take (second (first first-prog)) (length (rest first-prog))) (rest first-prog)) env))
                  (run-helper (list (list 'closure (list (append (list (first (first first-prog)))
                                             (list (list-tail (second (first first-prog)) (length rest-prog)))
                                                       (list (third (first first-prog)))))
                                          (run-helper (list (take (second (first first-prog)) (length rest-prog)) rest-prog) env)))
                  (run-helper (list (take (second (first first-prog)) (length rest-prog)) rest-prog) env))
                 )]   
                 [else
                  (run-helper
                   (list (list 'closure first-prog (run-helper (list (second (first first-prog)) (rest first-prog)) env)))
                   (run-helper (list (second (first first-prog)) (rest first-prog)) env))
                  ])))])]
              [(and (list? first-prog) (equal? (first first-prog) 'define)) ;For the define part
               (cond
                 [(hash-has-key? env (second first-prog)) (report-error 'duplicate-name (second first-prog))]
                 [(run-helper (list (list 'procedure? '(third first-prog))) env)
                  (run-helper rest-prog (hash-set env (second first-prog) (run-helper (list (third first-prog)) env)))]
                 [(and (list? (third first-prog)) (hash-has-key? env (first (third first-prog)))) ;(hash-ref env (first (third first-prog)))
                  (cond
                    [(run-helper (list (list 'procedure? (hash-ref env (first (third first-prog))))) env)
                     (run-helper rest-prog
                                 (hash-set env (second first-prog) (run-helper
                                                                    (list (append (list (hash-ref env (first (third first-prog)))) (remove (first (third first-prog)) (third first-prog)))) env)))
   
                     ]
                    [else (run-helper (list (third first-prog)) env)]
                    )]
                 [else
                  (run-helper rest-prog (hash-set env (second first-prog) (run-helper (list (third first-prog)) env)))
                  ])]
              [(and (list? first-prog) (equal? (first first-prog) '+)) ;For the builtin "+"
               (plus-helper (rest first-prog) env)
               ]
              [(and (list? first-prog) (equal? (first first-prog) '<)) ;For the builtin "<"
               (< (run-helper (second first-prog) env) (run-helper (third first-prog) env))
               ]
              [(and (list? first-prog) (equal? (first first-prog) 'equal?)) ;For the builtin "equal?"
               (equal? (run-helper (second first-prog) env) (run-helper (third first-prog) env))
               ]
              [(and (list? first-prog)(equal? 'lambda (first first-prog))) first-prog] ;For the procedure 
              [(and (list? first-prog) (equal? (first first-prog) 'procedure?)) (if (list? (second first-prog)) ;For the builtin "procedure?"
                                                                                    (if (equal? 'lambda (first (second first-prog))) #t #f)
                                                                                    (run-helper (list (list 'procedure? (run-helper (second first-prog) env))) env))]
  
              [(and (equal? 2 (length prog)) (list? first-prog) (list? (first rest-prog))) ;For the environment hash table
               (cond
                 [(null? (first rest-prog)) env]
                 [(equal? (length first-prog) 1) (hash-set env (first first-prog) (first (first rest-prog)))]
                 [else
                  (run-helper (list (rest first-prog)(rest (first rest-prog))) (hash-set env (first first-prog) (first (first rest-prog))))
                  ])]
              [(and (list? first-prog) (list? (first first-prog)) (hash-has-key? env (first (first first-prog))))
               ;For expressions like ((a) 3)
                  (run-helper (list (flatten first-prog)) env)]
              [(and (list? first-prog) (hash-has-key? env (first first-prog))) ;For the expression part like (a 3)
               (cond
                 [(hash-has-key? env (string->symbol (string-append (symbol->string (first first-prog))"-dc")));check if define-contract ID exist in expr, and check each subexpression of dc here
                  (cond
                    [(not (equal? (length (rest first-prog)) ;check the length of sub-expr list, and # of variables in the expr 
                                  (length (drop-right (hash-ref env (string->symbol (string-append (symbol->string (first first-prog))"-dc"))) 2))))
                     (report-error 'invalid-contract (first first-prog))]
                    [(not (list? (defcon-helper (rest first-prog) env
                                   (hash-ref env (string->symbol (string-append (symbol->string (first first-prog))"-dc"))) first-prog)))
                     (report-error 'contract-violation)]
                    [else
                     (if (run-helper (list (list (last (hash-ref env (string->symbol (string-append (symbol->string (first first-prog))"-dc"))))
                                                 (run-helper (list first-prog) (hash-remove env (string->symbol (string-append (symbol->string (first first-prog))"-dc")))))) env)
                         (run-helper (list first-prog) (hash-remove env (string->symbol (string-append (symbol->string (first first-prog))"-dc"))))
                         (report-error 'contract-violation)
                         )
                     ])]
                 [(run-helper (list(list 'procedure? (hash-ref env (first first-prog)))) env)
                  (run-helper (list (append (list (hash-ref env (first first-prog))) (remq (first first-prog) first-prog))) env)
                  ]
                 [else
                  (run-helper (list (third (first (second (first (hash-ref env (first first-prog)))))))
                              (run-helper (list (second (first (second (first (hash-ref env (first first-prog))))))(rest first-prog))
                                          (third (first (hash-ref env (first first-prog))))))])]
  
              [(and (list? first-prog) (equal? 'integer? (first first-prog))) (integer? (run-helper (rest first-prog) env))] ;For integer?
              [(and (list? first-prog) (equal? 'boolean? (first first-prog))) (boolean? (run-helper (rest first-prog) env))] ;For boolean?
              [(and (list? first-prog) (equal? 'any (first first-prog))) #t] ;For any

              [(and (list? first-prog) (equal? 'define-contract (first first-prog))) ;For Define-Contract
               (cond
                 [(hash-has-key? env (string->symbol (string-append (symbol->string (second first-prog))"-dc"))) (report-error 'invalid-contract (second first-prog))]
                 )
               (if (list? (defcon-checker (second first-prog) (third first-prog) env (third first-prog))) ;Check for errors in subexpr
                   (run-helper rest-prog (hash-set env (string->symbol (string-append (symbol->string (second first-prog))"-dc")) (third first-prog)))
                   (report-error 'invalid-contract (second first-prog))
                   )
               ]
              [else ;For anything else
               (cond
                 [(and (list? first-prog) (list? (first first-prog)) (member 'lambda (first first-prog)))
                  (print first-prog)]
                 [(and (list? first-prog) (list? (first first-prog)) (list? (first (first first-prog))))
                  (cond
                  [(and (member 'lambda  (first (first first-prog))) (empty? rest-prog))
                   (run-helper (list (append (first first-prog) (rest first-prog))) env)]
                  [(empty? rest-prog) (run-helper (list (flatten (append (first first-prog) (rest first-prog)))) env)]
                  [(empty? (rest first-prog)) (run-helper (list (append (first first-prog) rest-prog)) env)]
                  )]
                 [(> (length prog) 1) (report-error 'not-a-function first-prog)]
                 [(not(hash-has-key? env first-prog)) (report-error 'unbound-name first-prog)]
                 
                 )]
              ))])
  )

;--------------------------
;Test Cases
;--------------------------

;(run-interpreter '((define a 1)(define b #t)(define c #f) b))
;(run-interpreter '((+ 1 2 3 (+ 2 2) 5)))
;(run-interpreter '((+ (+ 20 20 20 20) 30 40 20 20 20)))
;(run-interpreter '((define a 1) (define b 2) (define c 3) (+ a b c)))
;(run-interpreter '((equal? 3 3)))
;(run-interpreter '(((lambda (x) (+ x 2)) 4)))
;(run-interpreter '((define a ((lambda (x) (+ x 1)) 1)) a))
;(run-interpreter '((procedure? (+ 1 3))))
;(run-interpreter '((define a (lambda () (+ 1 3))) (procedure? a)))
;(run-interpreter '((define a 10) b))
;(run-interpreter '(3 4 5))
;(run-interpreter '((define a ((lambda (x) (+ x 1)) 1)) a))
;(run-interpreter '((define a ((lambda (x y) (+ x y)) 1)) (a 10)))
;(run-interpreter '((define a ((lambda (x y z) (+ x y z)) 1 1)) (a 10)))
;(run-interpreter '((define a (lambda (x) x)) (a 1)))
;(run-interpreter '((define make-adder (lambda (n m) (+ n m)))
;                                  (define add-one (make-adder 1))
;(+ (add-one 5) (add-one 5))))
;                                   (define add-two (make-adder 2))
;                                    (+ (add-one 5) (add-two 10))))
;(run-interpreter '((boolean? #f)))
;(run-interpreter '((define a #t) (boolean? a)))
;(run-interpreter '((boolean? 2)))
;(run-interpreter '((define a 2) (integer? a)))
;(run-interpreter '((define-contract f (integer? -> boolean?))
;                                    (define f (lambda (x) (< x 4)))
;                                   (f 3)))
;(run-interpreter '((define-contract f (integer? (lambda (x) (< x 3)) integer? -> integer?))
;                                    (define f (lambda (x y z) (+ x y z)))
;                                  (f 1 1 1)))
;(run-interpreter '(((lambda (n n) (+ n n)) 1 2))) ;Curried error checking
;(run-interpreter '((define a (lambda (n n) (+ n n))) (a 1 2))) ;Curried error checking
;(run-interpreter '((((((lambda (n n) (+ n n)) 1) 2) 3)))) ;Problem as its flattened
;(run-interpreter '(((lambda (x) (+ x 1)) 1))) ;Basic Lambda
;(run-interpreter '(((lambda (a) ((lambda (b) ((lambda (c) (+ a b c)) 1) 1) 1))))) ;just fails
;(run-interpreter '((lambda (a) (+ a 3)) 4)) ;Doesn't work so don't care
;(run-interpreter '((((lambda (a) (+ a 3)))) 4)) ;should work if curried
;(run-interpreter '(((lambda (a) (+ a 4))) 4)) ;Need to check rest-prog in lambda
;(run-interpreter '((((lambda (a b) (+ a b))) 4 4)))
;(run-interpreter '(((lambda (a b) (+ a b)) 3) 5)) ;Need to check rest-prog in lambda
;(run-interpreter '((define curried (lambda (a b c d e f) (+ a b c d e f))) ((((((curried 1) 2) 3) 4) 5) 6)))
;(run-interpreter '((define curried (lambda (a b c d e f) (+ a b c d e f))) ((((((curried))))) 1 2 3 4 5 6)))
;(run-interpreter '((define f (lambda (a b) (+ a b))) ((f) 3 4)))
;(run-interpreter '((define f (lambda (a b) (+ a b))) ((f 3) 4)))
#|
(interpret env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Dubdub expression.

  Returest-progs the value of the Dubdub expression under the given environment.
|#
(define (interpret env expr)
  (void))


#|
Starter definition for a closure "struct". Racket structs behave similarly to
C structs (contain fields but no methods or encapsulation).
Read more at https://docs.racket-lang.org/guide/define-struct.html.

You can and should modify this as necessary. If you're having trouble working with
Racket structs, feel free to switch this implementation to use a list/hash instead.
|#
(struct closure (params body))
