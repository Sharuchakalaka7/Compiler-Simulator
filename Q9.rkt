#lang racket

(provide compile-simpl)

;; Question Q9
;; Compiler for converting SIMPL to A-PRIMPL
;; Author: Ahmed Shahriar




;;; SIMPL Language Grammar:
;;
;; program = (vars [(symbol number) ...]
;;                 stmt ...)
;;
;; stmt = (print aexp)
;;      | (print string)
;;      | (set symbol aexp)
;;      | (seq stmt ...)
;;      | (iff bexp stmt stmt)
;;      | (skip)
;;      | (while bexp stmt ...)
;;
;; aexp = number
;;      | symbol
;;      | (aop aexp aexp)
;;
;; bexp = boolean
;;      | (not bexp)
;;      | (and bexp bexp)
;;      | (or bexp bexp)
;;      | (baop aexp aexp)
;;
;; exp = aexp | bexp
;;
;; aop = + | - | * | div | mod
;;
;; baop = < | > | <= | >= | =
;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; COMPILING EXPRESSIONS ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Relative stack instructions in the context of A-PRIMPL
(define push `(add SP SP 1))
(define pop `(sub SP SP 1))
(define peek `(-1 SP))

;; trans-op: (union symbol proc) -> symbol
;; Translates the given SIMPL operator (arithmetic, boolean, and
;; comparisons) to its A-PRIMPL instruction equivalent
(define (trans-op op)
  (match op
    ['+   'add]
    ['-   'sub]
    ['*   'mul]
    ['/   'div]
    ['div 'div]
    ['mod 'mod]
    ['>   'gt]
    ['>=  'ge]
    ['<   'lt]
    ['<=  'le]
    ['=   'equal]
    ['not 'lnot]
    ['and 'land]
    ['or  'lor]
    [_ (error 'compile-simpl "Syntax Error - invalid op: ~a" op)]))




;; get-src1: exp -> (listof stmt[A-PRIMPL])
;; Returns the proper source code for the given expression which occur
;; as the first operand
(define (get-src1 x1)
  (cond
    [(list? x1)   (append (compile-exp (λ (x) empty) x1)
                          (list `(move ,peek (0 SP))))]
    [(symbol? x1) (list `(move ,peek ,(conv-var-id x1)))]
    [else         (list `(move ,peek ,x1))]))

;; get-src2: exp -> (listof stmt[A-PRIMPL])
;; Returns the proper source code for the given expression which occur
;; as the second operand
(define (get-src2 x2)
  (if (list? x2) (compile-exp (λ (x) empty) x2) empty))

;; get-src-op: symbol exp -> (listof stmt[A-PRIMPL])
;; Returns the A-PRIMPL source code for the actual operation given its second
;; operation and operation symbol
(define (get-src-inst op x2)
  (define arg2  ; argument in the place of operand 2
    (cond [(list? x2)   '(0 SP)]
          [(symbol? x2) (conv-var-id x2)]
          [else         x2]))
  (list (if (symbol=? op 'not)
            (list (trans-op op) peek arg2)
            (list (trans-op op) peek peek arg2))))

;; compile-exp-list: proc exp -> (listof stmt[A-PRIMPL])
;; Helper function for compile-exp - manages the list? case of compile-exp
(define (compile-exp-list host-stmt exp) ; `(print-val ,x) (+ (+ 1 2) (+ 3 4))
  (define (exp-not?) (empty? (cddr exp)))
  (append (list push)
          (if (exp-not?) empty (get-src1 (second exp)))
          (get-src2 (last exp))
          (get-src-inst (first exp) (last exp))
          (host-stmt peek)
          (list pop)))




;; compile-exp: proc exp -> (listof stmt[A-PRIMPL])
;; Compiles the respective SIMPL expression contained in a SIMPL stmt, host-stmt
;; (which must be passed as a procedure that must also return a stmt[A-PRIMPL]) to
;; replace it with its full compiled counterpart
(define (compile-exp host-stmt exp)
  (cond
    [(string? exp) (list `(print-string ,exp))]
    [(list? exp)   (compile-exp-list host-stmt exp)]
    [(symbol? exp) (host-stmt (conv-var-id exp))]
    [else          (host-stmt exp)]))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; COMPILING STATEMENTS ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; conv-var-id: symbol -> (union symbol boolean)
;; Returns the conventional SIMPL variable/boolean name in the A-PRIMPL context
(define (conv-var-id id)
  (cond
    [(symbol=? id 'true)  true]
    [(symbol=? id 'false) false]
    [else (string->symbol (string-append "_" (symbol->string id)))]))

;; compile-var: (pair symbol imm) -> stmt[A-PRIMPL]
;; Helper function for compile-vars
;; Produces the A-PRIMPL data pseudoinstruction for just one SIMPL
;; var declaration
(define (compile-var var)
  (define val
    (cond [(symbol? (second var)) (conv-var-id (second var))]
          [else                   (second var)]))
  `(data ,(conv-var-id (first var)) ,val))




;; compile-vars: (listof (pair symbol imm)) -> (listof stmt[A-PRIMPL])
;; Generates the data declarations for each initial variable declaration
;; in the program initial
(define (compile-vars vars)
  (if (empty? vars) empty
      (cons (compile-var (first vars))
            (compile-vars (rest vars)))))

;; compile-print: (union exp string) -> (listof stmt[A-PRIMPL])
;; Translates the contents of a print statement
(define (compile-print exp)
  (compile-exp (λ (x) (list `(print-val ,x))) exp))
  
;; compile-set: symbol exp -> (listof stmt[A-PRIMPL])
;; Translates the contents of a set statement
(define (compile-set id exp)
  (set! id (conv-var-id id))
  (compile-exp (λ (x) (list `(move ,id ,x))) exp))

;; compile-seq: (listof stmt[SIMPL]) -> (listof stmt[A-PRIMPL])
;; Translates the contents of a seq statement
(define (compile-seq stmts)
  (cond
    [(empty? stmts) empty]
    [else (append (compile-stmt (first stmts))
                  (compile-seq (rest stmts)))]))

;; compile-iif: exp stmt[SIMPL] stmt[SIMPL] -> (listof stmt[A-PRIMPL])
;; Translates the contents of an iif statement
(define (compile-iif exp tstmt fstmt)
  (define LABEL0 (gensym 'TRUE-))
  (define LABEL1 (gensym 'FALSE-))
  (define LABEL2 (gensym 'IIF-END-))
  (append (compile-exp (λ (x) (list `(branch ,x ,LABEL0))) exp)
          (list `(jump ,LABEL1)
                `(label ,LABEL0))
          (compile-stmt tstmt)
          (list `(jump ,LABEL2)
                `(label ,LABEL1))
          (compile-stmt fstmt)
          (list `(label ,LABEL2))))

;; compile-while: exp (listof stmt[SIMPL]) -> (listof stmt[A-PRIMPL])
;; Translates the contents of a while statement
(define (compile-while exp loop-body)
  (define LABEL0 (gensym 'LOOP-START-))
  (define LABEL1 (gensym 'LOOP-BODY-))
  (define LABEL2 (gensym 'LOOP-END-))
  (append (list `(label ,LABEL0))
          (compile-exp (λ (x) (list `(branch ,x ,LABEL1))) exp)
          (list `(jump ,LABEL2)
                `(label ,LABEL1))
          (compile-seq loop-body)
          (list `(jump ,LABEL0)
                `(label ,LABEL2))))




;; compile-stmt: stmt[SIMPL] -> (listof stmt[A-PRIMPL])
;; Translates just one SIMPL statement into its A-PRIMPL counterpart source code
;; This function is meant to recursively produce the source code inside each
;; SIMPL statement
(define (compile-stmt stmt)
  (match stmt
    [`(skip) empty] ; same effect as void
    [`(print ,exp)        (compile-print exp)]
    [`(set ,id ,exp)      (compile-set id exp)]
    [`(seq ,stmt1 ...)    (compile-seq (rest stmt))]
    [`(iif ,exp ,tp ,fp)  (compile-iif exp tp fp)]
    [`(while ,exp ,s ...) (compile-while exp (cddr stmt))]
    [_ (error 'compile-stmt "Syntax Error - invalid stmt: ~a" stmt)]))




;;;;;;;;;;;;;;;;;;;;;;;
;;;; MAIN COMPILER ;;;;
;;;;;;;;;;;;;;;;;;;;;;;


;; compile-simpl: program[SIMPL] -> (listof stmt[A-PRIMPL])
;; Compiles the given SIMPL code to an equivalent corresponding A-PRIMPL code
(define (compile-simpl prog)
  (match prog
    [`(vars ,_) empty]
    [`(vars ,vars ,_ ...)
       ((λ (x) (if (empty? x) empty
          (append x                        ; compiled source code for statements
                  (list `(halt))           ; halt command
                  (compile-vars vars)      ; compiled data (vars) pseudoinstructions
                  (list `(data SP STACK))  ; initially pointing to beginning of stack
                  (list `(label STACK))))) ; start of stack area
        (compile-seq (cddr prog)))]
    [_ (error 'compile-simpl "Syntax Error - improper initial")]))






  