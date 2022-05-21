#lang racket

(require "SIMPLsimulator.rkt")
(require "PRIMPLsimulator.rkt")
(require "Q9.rkt")
(require "Q8.rkt")

;;; Driver file for Question Q9




;;; EXAMPLES
;;; Note that all tests technically test the (seq stmt ...) statement implicitly

;; Example 1: vars test
(define s1
  `(vars [(i 1) (j 2) (k 3)] (skip)))
(define a1
  `((halt)
    (data _i 1)
    (data _j 2)
    (data _k 3)))
(define p1
  `(0 1 2 3))

;; Example 2: (print aos) test
(define s2
  `(vars [(i 1) (j 2) (k 3)]
         (print i)
         (print "\n")
         (print j)
         (print "\n")
         (print k)
         (print "\n")))
(define a2
  `((print-val _i)
    (print-string "\n")
    (print-val _j)
    (print-string "\n")
    (print-val _k)
    (print-string "\n")
    (halt)
    (data _i 1)
    (data _j 2)
    (data _k 3)))
(define p2
  `((print-val (7))
    (print-string "\n")
    (print-val (8))
    (print-string "\n")
    (print-val (9))
    (print-string "\n")
    0
    1
    2
    3))

;; Example 3: aexp test
(define s3
  `(vars [(a 5) (b 10)]
         (print a)
         (print "\n")
         (print b)
         (print "\n")
         (print (div (+ (+ a b) (+ a b)) 4))
         (print "\n")
         (print "\n")))
(define a3
  `((print-val _a)
    (print-string "\n")
    (print-val _b)
    (print-string "\n")
    (add SP SP 1)
    (add SP SP 1)
    (add SP SP 1)
    (move (-1 SP) _a)
    (add (-1 SP) (-1 SP) _b)
    (sub SP SP 1)
    (move (-1 SP) (0 SP))
    (add SP SP 1)
    (move (-1 SP) _a)
    (add (-1 SP) (-1 SP) _b)
    (sub SP SP 1)
    (add (-1 SP) (-1 SP) (0 SP))
    (sub SP SP 1)
    (move (-1 SP) (0 SP))
    (div (-1 SP) (-1 SP) 4)
    (print-val (-1 SP))
    (sub SP SP 1)
    (print-string "\n")
    (print-string "\n")
    (halt)
    (data _a 5)
    (data _b 10)
    (data SP STACK)
    (label STACK)))
(define p3 (primpl-assemble a3))

;; Example 4: (set id aexp) test
(define s4
  `(vars [(a 63) (b 43) (avg 0)]
         (print avg)
         (print "\n")
         (set avg (div (+ (+ a b) (+ b b)) 4))
         (print avg)))
(define a4
  `((print-val _avg)
    (print-string "\n")
    (add SP SP 1)
    (add SP SP 1)
    (add SP SP 1)
    (move (-1 SP) _a)
    (add (-1 SP) (-1 SP) _b)
    (sub SP SP 1)
    (move (-1 SP) (0 SP))
    (add SP SP 1)
    (move (-1 SP) _b)
    (add (-1 SP) (-1 SP) _b)
    (sub SP SP 1)
    (add (-1 SP) (-1 SP) (0 SP))
    (sub SP SP 1)
    (move (-1 SP) (0 SP))
    (div (-1 SP) (-1 SP) 4)
    (move _avg (-1 SP))
    (sub SP SP 1)
    (print-val _avg)
    (halt)
    (data _a 63)
    (data _b 43)
    (data _avg 0)
    (data SP STACK)
    (label STACK)))
(define p4 (primpl-assemble a4))

;; Example 5: (seq stmt ...) test
(define s5
  `(vars [(x 0)]
         (seq
            (set x 2)
            (set x (* x x))
            (set x (* x x)))
         (print x)
         (print "\n")))
(define a5
  `((move _x 2)
    (add SP SP 1)
    (move (-1 SP) _x)
    (mul (-1 SP) (-1 SP) _x)
    (move _x (-1 SP))
    (sub SP SP 1)
    (add SP SP 1)
    (move (-1 SP) _x)
    (mul (-1 SP) (-1 SP) _x)
    (move _x (-1 SP))
    (sub SP SP 1)
    (print-val _x)
    (print-string "\n")
    (halt)
    (data _x 0)
    (data SP STACK)
    (label STACK)))
(define p5 (primpl-assemble a5))

;; Example 6...
(define s6
  `(vars [(x 100) (y 1)]
         (while (> x 0)
                (set y (* 2 y))
                (set x (- x 1)))
         (print y)))

;; Example 7...
(define s7
  `(vars [(n 10) (fj 1) (fjm1 0) (t 0) (ans 0)]
         (iif (= n 0)
              (set ans fjm1)
              (seq
               (while (> n 1)
                      (set t fj)
                      (set fj (+ fj fjm1))
                      (set fjm1 t)
                      (set n (- n 1)))
               (set ans fj)))
         (print ans)))

;; Example 8: bexp test
(define s8
  `(vars [(n 5)]
         (while (or (> n 0) (= n 0))
                (print n)
                (print "\n")
                (set n (- n 1)))
         (print "\n")))

;; Example 9: bexp test #2 - logical xor
(define s9
  `(vars [(A false) (B false)]  ; 11000101
         (print (and (or A B) (not (and A B))))
         (print "\n")))
         




;;; TESTING

(define (run-primp-test prog)
  (load-primp prog)
  (run-primp))

(define (run-half-test a-prog)
  (run-primp-test
     (primpl-assemble
        a-prog)))

(define (run-full-test s-prog)
  (run-primp-test
     (primpl-assemble
        (compile-simpl
           s-prog))))

(define (main-test sp ap pp)
  (printf "~a\n" (equal? ap (take (compile-simpl sp) (length ap))))
  (printf "~a\n" (equal? pp (take (primpl-assemble (compile-simpl sp))
                                  (length pp)))))




#|
at
(newline)

(take (compile-simpl st) 20); (+ 3 (length at)))
(newline)
pt
(newline)

(take (primpl-assemble (compile-simpl st)) 20); (+ 3 (length pt)))
(newline)
(main-test st at pt)
(newline)
|#






;; Current Test(s):

(run-full-test s9)









