#lang racket #| CSC324 Fall 2019: Exercise 1 |#
#|
* Before starting, please review the exercise guidelines at
http://www.cs.toronto.edu/~lczhang/324/homework.html *

In this part of the exercise, you'll get started writing some simple
functions in Racket. Since this is likely your first time using Racket,
we strongly recommend going through some of the documentation we listed
under the "Software" page as you work through this exercise.
In comments below, we also give some links to documentation to built-in
functions for standard data types (numbers, strings, lists) that we want
you to become familiar with.

Finally, you'll notice the (module+ test ...) expressions interleaved with
the function definitions; this is a standard Racket convention for simple
unit tests that we'll use throughout the course. Please read them carefully,
and add tests of your own!
|#
;-------------------------------------------------------------------------------
; This expression exports functions so they can be imported into other files.
; Don't change it!
(provide celsius-to-fahrenheit n-copies num-evens num-many-evens double-list
         calculate calculate-many)


; We use (module+ test ...) to mark code that shouldn't be evaluated when this
; module is imported, but instead is used for testing purposes (similar to Python's
; if __name__ == '__main__').
;
; Right now each module+ expression after this one (i.e., the ones that actually
; contain test cases) is commented out, because they all fail, and DrRacket runs
; tests automatically when you press "Run".
; As you do your work, uncomment the module+ expression by deleting the `#;` in
; front of the module+ expressions and run the module to run the tests.
;
; NOTE: As is common to testing frameworks, by default DrRacket only displays
; output for *failing* tests. If you run the module with the tests uncommented
; but don't see any output, that's good---the tests all passed! (If you want
; to double-check this, you can try breaking a test case and seeing the "fail"
; output yourself.)
(module+ test
  ; Import the testing library
  (require rackunit))

;-------------------------------------------------------------------------------
; * Task 1: Working with Racket
;-------------------------------------------------------------------------------


#|
(celsius-to-fahrenheit temp)
  temp: an integer, representing a temperature in degrees Celsius

  Returns the equivalent temperature in degrees fahrenheit, rounded to the
  nearest integer.

  Relevant documentation: https://docs.racket-lang.org/reference/generic-numbers.html.
|#
(define (celsius-to-fahrenheit temp)
  ; TODO: replace the (void) with a proper function body.
  (round(+(* temp 9/5) 32)))

(module+ test
    ; We use rackunit's test-equal? to define some simple tests.
    (test-equal? "(celsius-to-fahrenheit 0)"  ; Test label
                 (celsius-to-fahrenheit 0)    ; Actual value
                 32)                         ; Expected value
    (test-equal? "(celsius-to-fahrenheit 14)"
                 (celsius-to-fahrenheit 14)
                 57)
    (test-equal? "(celsius-to-fahrenheit -100)"
                 (celsius-to-fahrenheit -100)
                 -148)
    (test-equal? "(celsius-to-fahrenheit 37)"
                 (celsius-to-fahrenheit 37)
                 99)
    (test-equal? "(celsius-to-fahrenheit 38)"
                 (celsius-to-fahrenheit 38)
                 100))

;-------------------------------------------------------------------------------

#|
(n-copies s n)
  s: a string
  n: a non-negative integer n

  Returns a string consisting of n copies of s.
  *Use recursion!* Remember that you aren't allowed to use mutation for this exercise.

  Relevant documentation: https://docs.racket-lang.org/reference/strings.html
|#
(define (n-copies s n)
  (cond
    [(equal? n 0) ""]
    [(equal? n 1) s]
  [else (string-append s (n-copies s (- n 1)))]
))

(module+ test
    (test-equal? "n-copies: Three copies"
                 (n-copies "Hello" 3)
                 "HelloHelloHello")
    (test-equal? "n-copies: Zero copies"
                 (n-copies "Hello" 0)
                 "")
    (test-equal? "n-copies: Single letter"
                 (n-copies "a" 10)
                 "aaaaaaaaaa"))

;-------------------------------------------------------------------------------

#|
(num-evens numbers)
  numbers: A list of integers.

  Returns the number of even elements in the list.

  Relevant documentation: https://docs.racket-lang.org/reference/pairs.html.

  Reminder: do not use mutation or loop constructs here.
  Instead, use the basic *recursive* template on lists, which we've started
  for you in the commented code below.
|#
(define (num-evens numbers)
  (cond
    [(null? numbers) 0]
    [else
     ; In this case the list is non-empty. Divide the list into its first
     ; element and the remaining numbers in the list, recurse on the remaining,
     ; and combine the results in some way to return the final result.
     (let ([first-number (first numbers)]
           [rest-number (num-evens (rest numbers))])  ; Pick a better variable name.
        (+  rest-number(if(equal? (modulo first-number 2) 0) 1 0)))]))

#|
(num-many-evens lists-of-numbers)
  lists-of-numbers: A list of lists of integers.

  Return the number of inner lists that contain three or more even integers.

  Hint: you can use a very similar approach to the previous function.
|#
(define (num-many-evens lists-of-numbers)
  (cond
    [(null? lists-of-numbers) 0]
    [else 
    (let ([first-number (first lists-of-numbers)] [rest-number (rest lists-of-numbers)])
    (if (list? first-number) (+ (if (<= 3 (num-evens first-number)) 1 0))
        (num-many-evens (rest-number))))]))

(module+ test
    (test-equal? "num-evens: empty list"
                 (num-evens null)
                 0)
    (test-equal? "num-evens: simple non-empty list"
                 (num-evens (list 1 2 4))
                 2)

    (test-equal? "num-many-evens: empty list"
                 (num-many-evens null)
                 0)
    (test-equal? "num-many-evens: simple non-empty list"
                 (num-many-evens (list (list 2 4 5 7 8)))
                 1))

;-------------------------------------------------------------------------------

#|
(double-list numbers)
  numbers: A list of integers.

  Returns a new list, whose elements are double the elements in numbers.

  Relevant documentation: https://docs.racket-lang.org/reference/pairs.html.

  Reminder: do not use mutation or loop constructs here.
  Instead, use the basic *recursive* template on lists, which we've started
  for you in the commented code below.
|#

(define (double-list numbers)
  (if (null? numbers)
      (list); What should this be?
      (cons (* 2 (first numbers)) (double-list (rest numbers)))) ; Hint: construct a list out of the first part of
                  ;       the answer, and use recursion for the rest
                  ;       of the answer.
  )

(module+ test
  (test-equal? "double-list: empty list"
               (double-list null)
               null)
  (test-equal? "double-list: non-empty list"
               (double-list (list 3 4 5))
               (list 6 8 10)))

;-------------------------------------------------------------------------------
; * Task 2: Calculator I
;-------------------------------------------------------------------------------

#|
(calculate expr)
  expr: An expression generated by the Binary Arithmetic Expression Grammar
        described in the handout.

  Return the numerical value of the expression
|#
(define (calculate expr)
  (cond
    [(null? expr) 0]
    [else (let ([first-number (first expr)] [rest-number (rest expr)])
    (if (and (pair? (first rest-number)) (symbol? first-number)) (calculate (first rest-number))
        ;(when (symbol? first-number)
         (cond [(equal? first-number '+) (+ (car rest-number)(cadr rest-number))]
          [(equal? first-number '-) (- (car rest-number)(cadr rest-number))]
          [(equal? first-number '/) (/ (car rest-number)(cadr rest-number))]
          [(equal? first-number '*) (* (car rest-number)(cadr rest-number))]);)
        ))]))

(module+ test
    (test-equal? "calculate: +"
                 (calculate '(+ 2 3)) ;'(+ 2 3) is the same as (list '+ 2 3)
                 5)
    (test-equal? "calculate: /"
                 (calculate '(/ (+ 2 6) 2))
                 4))

#|
(calculate-many exprs)
  exprs: A list of expressions, each generated from the
         Binary Arithmetic Expression Grammar described
         in the handout.

  Returns a list containing the values of each the expressions.
|#
(define (calculate-many exprs)
  (void))

#;(module+ test
    (test-equal? "calculate-many:"
                 (calculate-many '((+ 2 3) (/ (+ 2 6) 2))) ; '((+ 2 3) (/ 8 2)) is the same as
                 '(5 4)))                            ; (list (list '+ 2 3) (list '/ 8 2))
