#lang racket
(provide eval-for-meta           ; evaluate expression in given phase and return result
         eval-for-syntax         ; evaluate expression in phase 1 and return result
         eval-form-for-meta      ; evaluate form in given phase
         eval-form-for-syntax    ; evaluate form in phase 1
         syntax-value            ; return the value associated with a syntax binding in a given phase
         )

(require (for-meta 2 racket/base))

; phase-lift-form : nonnegative-integer s-exp -> s-exp
;   wrap p layers of  (begin-for-syntax _) around form
(define (phase-lift-form p form)
  (cond [(= p 0) form]
        [else    (phase-lift-form (- p 1) #`(begin-for-syntax #,form))]))

; phase-lift-expression : nonnegative-integer s-exp continuation -> s-exp
;   wrap expr in p let-syntax with a body of `(,return ,expr)
;   When the return result is evaluated, expr gets evaluated in phase p
;   and its return value is passed to return.
(define (phase-lift-expression p expr return)
  (define m (gensym 'm))
  (define _ (gensym '_))
  (let loop ([initial #t] [p p] [expr expr])
    (cond [initial  (loop #f    p    #`(#,return #,expr))]
          [(= p 0)  expr]             
          [return   (loop #f (- p 1) #`(let-syntax ([#,m (lambda (#,_) #,expr)]) (#,m)))])))

; eval-for-meta : phase expression namespace -> value
;   returns the result of evaluating the expression expr 
;   in phase p (relative to the current phase) using the namespace ns
(define (eval-for-meta p expr [ns (current-namespace)])
  (let/ec return
    (eval (phase-lift-expression p expr return) ns)))

; eval-for-syntax : expression namespace escape -> value
;   like eval-for-meta with phase fixed to 1
(define (eval-for-syntax expr [ns (current-namespace)])
  (eval-for-meta 1 expr ns))

; eval-form-for-meta : phase form namespace -> void
;   evaluates the form in phase p using the namespace ns
(define (eval-form-for-meta p form [ns (current-namespace)])
  (eval (phase-lift-form p form) ns))

; eval-form-for-syntax : form namespace -> void
;   like eval-form-for-meta for phase 1
(define (eval-form-for-syntax form [ns (current-namespace)])
  (eval-form-for-meta 1 form ns))

; syntax-value : identifier [namespace] [phase] -> value
;   given an identifier bound to syntax in phase p,
;   return the value to which it is bound
(define (syntax-value id [p 0] [ns (current-namespace)])
  (eval-for-meta (+ p 1) #`(syntax-local-value #'#,id)))

(define (transformer id [ns (current-namespace)] [p 0])
  (syntax-value id p ns))

;;;
;;; TESTS
;;;

#;(

(require (for-meta 1 racket/base)
         (for-meta 2 racket/base)
         (for-meta 3 racket/base))

(begin-for-syntax     ; phase 1
  (begin-for-syntax   ; phase 2
    (define x 40)))   ; define x in phase 2

; set current-namespace to "here" (i.e. insides this module)
(define ns (variable-reference->namespace (#%variable-reference)))
(current-namespace ns)

(eval-form-for-meta 2 '(define y 41))
(eval-for-meta 2 '(list x y))



(define t (transformer #'or))
(define examples (list #'(or)
                       #'(or x)
                       #'(or x y)
                       #'(or x y z)
                       #'(or x (or y z))))

(map (compose1 syntax->datum t) examples)

; Result
#;'(#f
    (#%expression x)
    (let ((or-part x)) (if or-part or-part (or y)))
    (let ((or-part x)) (if or-part or-part (or y z)))
    (let ((or-part x)) (if or-part or-part (or (or y z)))))

)