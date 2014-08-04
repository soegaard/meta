#lang racket
(require (for-syntax syntax/parse)
         syntax/stx)

(provide stx-list stx-cons stx-list-rest)

(define-match-expander stx-list
  (lambda (pat-stx)
    (syntax-parse pat-stx
      [(_ elts ...)
       #'(? stx-list? (app stx->list (list elts ...)))]
      [_
       (error 'stx-list "error in match pattern" pat-stx)])))

(define-match-expander stx-list-rest
  (lambda (pat-stx)
    (syntax-parse pat-stx
      [(_ elts ...)
       #'(? stx-pair? (app stx->list-rest (list-rest elts ...)))]
      [_
       (error 'stx-list-rest "error in match pattern" pat-stx)])))

(define-match-expander stx-cons
  (lambda (pat-stx)
    (syntax-case pat-stx ()
      [(_ elt0 elt1)
       #'(? stx-pair? (app stx->cons (cons elt0 elt1)))])))

(define (stx->cons x)
  (cons (stx-car x) (stx-cdr x)))

(define (stx->list-rest x)
  (if (stx-pair? x)
      (cons (stx-car x) (stx->list-rest (stx-cdr x)))
      x))


; (provide <let-values> ...)

; syntax: (define-identifier-matcher name id)
;   define name as a match-expander, where
;   (name)    matches id
;   (name y)  mateches id and binds y to the matched value
;   name is provided
(define-syntax (define-identifier-matcher stx)
  (syntax-parse stx
    [(_ name id)
     #'(begin
         (define (predicate? x)
           (and (identifier? x)
                (bound-identifier=? x id)))
         (provide name)
         (define-match-expander name
           (λ (pat-stx)
             (syntax-case pat-stx ()
               [(_)   #'(? predicate?)]
               [(_ y) #'(? predicate? y)]
               [else (error 'name)]))))]))

(define-identifier-matcher <#%expression>           #'#%expression)
(define-identifier-matcher <module>                 #'module)
(define-identifier-matcher <#%plain-module-begin>   #'plain-module-begin)
(define-identifier-matcher <begin>                  #'begin)
(define-identifier-matcher <begin-for-syntax>       #'begin-for-syntax)
(define-identifier-matcher <#%provide>              #'provide)
(define-identifier-matcher <#%declare>              #'#%declare)
(define-identifier-matcher <#%define-values>        #'define-values)
(define-identifier-matcher <#%define-syntaxes>      #'define-syntaxes)
(define-identifier-matcher <#%require>              #'#%require)
(define-identifier-matcher <#%plain-lambda>         #'#%plain-lambda)
(define-identifier-matcher <case-lambda>            #'case-lambda)
(define-identifier-matcher <if>                     #'if)
(define-identifier-matcher <begin0>                 #'begin0)
(define-identifier-matcher <let-values>             #'let-values)
(define-identifier-matcher <letrec-values>          #'letrec-values)
(define-identifier-matcher <set!>                   #'set!)
(define-identifier-matcher <quote>                  #'quote)
(define-identifier-matcher <quote-syntax>           #'quote-syntax)
(define-identifier-matcher <with-continuation-mark> #'with-continuation-mark)
(define-identifier-matcher <#%plain-app>            #'#%plain-app)
(define-identifier-matcher <#%top>                  #'#%top)
(define-identifier-matcher <#%variable-reference>   #'#%variable-reference)


;;; The example used to define define-identifier-matcher
#;(define (let-values-keyword? x)
    (and (identifier? x) (bound-identifier=? x #'let-values)))

#;(define-match-expander <let-values>
  (λ (pat-stx)
    (syntax-case pat-stx ()
      [(_)    #'(? let-values-keyword?)]
      [(_ id) #'(? let-values-keyword? id)]
      [else (error)])))

; Test should evaluate to #t
#;(and (match #'x          [(<let-values>) #f] [_ #t])
     (match #'let-values [(<let-values>) #t] [_ #f])
     (let ([let-values 1])
       ; let-values is now different from kernel let-values
       ; so the following should not match
       (and (match #'x          [(<let-values>) #f] [_ #t])
            (match #'let-values [(<let-values>) #f] [_ #t]))))





