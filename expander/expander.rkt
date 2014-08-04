#lang racket

;;; THIS IS A WORK IN PROGRESS

;;;
;;; Macro Expander for Racket
;;;

; Racket's normal expander are implemented in C.
; This is an attempt to implement expand in Racket.

; This version focuses on the expansion of kernel forms.
; Currently standard syntax objects are used.
; New marks can be applied with syntax-introducers.
; Renamings are trickier, so either I might implement syntax 
; objects as structs. The downside of doing so is that
; it makes more difficult to call transformers imported
; from modules compiled with the real expander.

; Next up:  1) Introduce fresh identifiers in let-values and lambda
;           2) Introduce expansion contexts.
;           3) Support syntax-local- constructs
;           4) Implement syntax-objects
;           5) Implement namespaces (and module registry)

;;;
;;; TRACE
;;;

(define trace displayln)
; (define trace void)

;;;
;;; IMPORTS
;;;

(require (for-syntax syntax/parse)
         (for-meta 2 racket/base)
         syntax/modresolve
         syntax/strip-context         ; for strip-context
         syntax/stx
         "matchers.rkt")

; kernel-form-identifier-list is only used to catch unimplemented core syntax
(require (only-in syntax/kerncase kernel-form-identifier-list)) 

;;;
;;; BINDINGS
;;;

; An identifier is a name. Locations are cells in which a value is stored.
; An identifier that names a location is called a variable.
; An identifier that names syntax is called a syntactic keyword.
; An identifier is bound to the location.

; To find the location to which an identifier is bound is a two step process. 
; First the label of identifier is determined, then the label is looked up
; in the environment.

; For identifiers represented as real syntax objects, the label is 
; returned by identifier-binding-symbol.
(define (id-label x) (identifier-binding-symbol x))

; The same identifier can be bound in more than one phase.
; So either we need separate environments for each phase,
; or we need to associate a phase with each binding.
; Here we choose one environment and record the phase
; in which the label is associated to the label.

; The environment maps labels to bindings.
(struct environment (associations) #:transparent)
; associations are lists of elements of the form (list p id l b)
; where p  is a phase (integer or #f),
;       id is an identifier (needed for reification when using real eval)
;       l  is a label,
;       b  is a binding: lexical, macro

(struct binding (value)    #:mutable #:transparent)
(struct lexical binding () #:mutable #:transparent)
(struct macro   binding () #:mutable #:transparent)
; Syntax bindings are called "macro" here, since the 
; name syntax is used to create syntax-objects.

(define (local-eval x r [ns (current-namespace)])
  (eval (reify-environment x r) ns))

(define (reify-environment x r)
  (define (reify as x)
    (match as
      ['() x]
      [(cons (list p id l (lexical v)) as)
       (cond [(= p 0) (reify as #`(let ([#,id #,v]) #,x))]
             [else (error)])] ; possible?
      [(cons (list p id l (macro v)) as)
       (cond [(= p 0) (reify as #`(let-syntax ([#,id #,v]) #,x))]
             [else (error)])]
      [else (error)]))
  (match-define (environment as) r)
  (reify as x))


(define empty-environment (environment '()))

; extend the environment with a binding b with label l,
; for id in phase p 
(define (extend r p id l b)
  (unless (binding? b) (error (list id b)))
  (match-define (environment as) r)  
  (environment (cons (list p id l b) as)))

(define (extend* env p ids ls bs)
  (unless (list? bs) (error))
  (for/fold ([env env]) ([id (in-list ids)] [l (in-list ls)] [b (in-list bs)])
    (extend env p id l b)))

(define (extend** env p idss lss bss)
  (unless (andmap list? bss) (error bss))
  (unless (andmap list? lss) (error lss))
  (for/fold ([env env]) ([ids (in-list idss)] [ls (in-list lss)] [bs (in-list bss)])
    (extend* env p ids ls bs)))

(define (genlex)
  (lexical #f))

(define (genlex* is)
  (for/list ([i (in-list is)])
    (genlex)))

(define (genlex** iss)
  (for/list ([is (in-list iss)])
    (genlex* is)))

(define (genmac [v #f])
  (macro v))

(define (genmac* is [vs #f])
  (if vs
      (for/list ([i (in-list is)] [v (in-list vs)])
        (genmac v))
      (for/list ([i (in-list is)])
        (genmac))))

(define (genmac** iss [vss #f])
  (if vss
      (for/list ([is (in-list iss)] [vs (in-list vss)])
        (genmac* is vs))
      (for/list ([is (in-list iss)])
        (genmac* is))))

(define (genlab)
  (gensym 'l))

(define (genlab* is)
  (for/list ([i (in-list is)])
    (genlab)))

(define (genlab** iss)
  (for/list ([is (in-list iss)])
    (genlab* is)))



; find a binding associated with id in phase p,
; return #f id is unbound in phase p
(define (lookup env phase id)
  (match-define (environment as) env)
  (for/first ([a (in-list as)]
              #:when (let()
                       (match-define (list p i l b) a)
                       (and (= p phase)
                            (free-identifier=? i id))))
    (match-define (list p i l b) a)
    b))

; bindings can be top-level, module-level or lexical
(define (has-nontop-binding? id p)
  (identifier-binding id p))

; Note: has-nontop-binding? also works, when id is lexically bound to syntax
; > (let-syntax ([m (lambda (stx) #'42)])
;    (identifier-binding #'m))
; 'lexical

(require "transformer.rkt")

(define (bound? r p id)
  (or (lookup r p id)                                                     ; lexical
      (if (= p 0)
          (or (identifier-binding id)                                     ; module
              (namespace-variable-value (syntax->datum id) #f (λ () #f))) ; top-level
          (eval-for-meta 
           p #`(or (identifier-binding #'#,id)
                   (namespace-variable-value (syntax->datum #'#,id) #f (λ () #f)))))))

(define (unbound? r p id)
  (not (bound? r p id)))


; top-identifier-type : identifier phase -> (or #f 'syntax (list value))
;   given an identifier id determine whether x is value or syntax bound in phase p
;     assumption:  (identifier-binding id) returns #f
;     return #f        if id is unbound in phase p in namespace
;            'syntax   if id is bound to syntax (most often the value is a transformer)
;            (list v)  if id is bound to the value v
(define (top-identifier-type id p)
  (unless (= p 0) (error))
  (with-handlers ([exn:fail:syntax?            (λ (e) 'syntax)]
                  [exn:fail:contract:variable? (λ (e) #f)])
    (define sym (syntax->datum id)) ; TODO: substitutions ?
    (list (namespace-variable-value sym #t))))

(define (lexical-identifier-type id p env)
  (lookup env p id))

; module-identifier-type : identifier phase binding-info -> (or 'kernel 'syntax (list value))
;   the binding-info in b is the output of (identifier-binding id)
(define (module-identifier-type id p b)
  (displayln (list 'module-identifier-type id p b))
  (match-define (list src-mod src-id _ _ src-phase _ _) b)
  (define rmpi (resolve-module-path-index src-mod #f))
  (match rmpi
    ['#%kernel (list src-id 'kernel)]
    [_ (with-namespace (module->namespace rmpi)
         (with-handlers ([exn:fail:syntax?            (λ (e) 'syntax)]
                         [exn:fail:contract:variable? (λ (e) (error "internal error"))])
           (if (= p 0)
               (list (namespace-variable-value src-id #t))
               (eval-for-meta p #`(namespace-variable-value #,src-id #t)))))]))

; identifier-top-binding : identifier phase -> (or/c #f 'syntax 'value)
;   return #f        if id is unbound in phase in namespace
;          'syntax   if id is bound to syntax (most often the value is a transformer)
;          (list v)  if id is bound to the value v
(define (identifier-top-binding id p)
  (unless (= p 0) (error))
  (define b (identifier-binding id))
  (match b
    [#f #f]
    ['lexical (error 'identifier-top-binding "expected nonlexical identifier: ~a" id)]
    [else 
     (with-namespace (module->namespace (first b))
       (with-handlers ([exn:fail:syntax?            (λ (e) 'syntax)]
                       [exn:fail:contract:variable? (λ (e) #f)])
         (define sym (syntax->datum id)) ; TODO: substitutions ?
         (list (namespace-variable-value sym #t))))]))

; syntax-value : identifier phase -> value
;   given an identifier id bound to syntax in phase p,
;   return the value associated with p (most often a transformer)
#;(define (syntax-value id p)
  ; for an identifier id bound to syntax in phase p,
  ; get the value (most commonly a syntax transformer)
  (unless (= p 0) (error)) ; not implemented for p>0 yet
  (let/ec return
    (eval `(let-syntax ([m (λ(_) (,return (syntax-local-value #',id)))]) (m))
          (variable-reference->namespace (#%variable-reference)))))


; kernel-form-identifier? : identifier -> boolean
;  
(define kernel-form-identifier? 
  (let ()
    (define kernel-form-identifiers (kernel-form-identifier-list))
    (λ (xid)
      (memf (λ(kid) (free-identifier=? xid kid))
            kernel-form-identifiers))))

;;;
;;; NOTES
;;;


; parameter: syntax-local-phase-level
;   During the dynamic extent of a syntax transformer application by the expander, 
;   the result is the phase level of the form being expanded. Otherwise, the result is 0.

; parameter: syntax-local-context
;   (or/c 'expression 'top-level 'module 'module-begin list?)
;   Returns an indication of the context for expansion that triggered a syntax transformer call. 

; parameter: syntax-local-name
;   Returns an inferred name for the expression position being transformed, 
;   or #f if no such name is available.

;;;
;;;
;;;

; (syntax-track-origin new-stx orig-stx id-stx)
;   Adds properties to new-stx in the same way that macro expansion 
;   adds properties to a transformer result. 

; syntax: (with-namespace ns body ...+)
;   parameterize current-namespace to ns, and evalute bodies
(define-syntax (with-namespace stx)
  (syntax-parse stx
    [(_ ns body ...+) 
     #'(parameterize ([current-namespace ns])
         body ...)]))

; syntax: namespace-here
;   evaluates to the namespace of the top-level or module-top-level
(define-syntax (namespace-here stx)
  (with-syntax ([anchor (syntax-local-lift-expression #'(#%variable-reference))])
    #'(variable-reference->namespace anchor)))


(define (apply-unless p f v)
  (if (p v) v (f v)))

(define (apply-when p f v)
  (if (p v) (f v) v))

(define (sym-or-id? x)
  (or (symbol? x) (and (syntax? x) (symbol? (syntax-e x)))))

;;;
;;; EXPANSION
;;;

; Expansion begins with a top-level-form.
; Expansion always takes place in the context of a namespace.
; A namespace associates symbols with identifiers. 
; A namespace is a *top-level* concept and must not be confused 
; with an environment (which tracks local bindings).
; Example: To (expand '(+ 1 2)) the '+ needs to be associated
; with the addition primitive. In a base namespace we get
;     > (~id (namespace-symbol->identifier '+))
;     '(+ (#%kernel + #<path:.../racket/main.rkt> + 0 0 0))
; The source module is #%kernel in which it was called +
; and it was imported to the current namespace from "main.rkt"
; where the name also was +. All imports and exports were in phase 0.

; Unless a compiled datum (the original expression were expanded
; before ut was compiled) or a or a module form (whose meaning
; is independent on the bindings of the current namespace)
; the entire top-level-form is enriched with the lexical information 
; of the current-namespace.

(define (meta-expand top-level-form [ns (current-namespace)])
  (define phase 0)
  (with-namespace ns
    (continue (enrichen-top-level-form top-level-form) 
              phase
              empty-environment)))


(define (enrichen-top-level-form top-level-form)
  ; see docs for eval
  (define introduce namespace-syntax-introduce)
  (match top-level-form
    [(? syntax? s)
     (match (syntax-e s)
       [(? compiled-expression? c) c]
       [(cons (? sym-or-id? mod?) more)
        (define mod (introduce mod?))
        (if (bound-identifier=? mod #'module)
            (datum->syntax #f (cons mod more))
            (introduce s))]
       [_ (introduce s)])]
    [d (enrichen-top-level-form (datum->syntax #f d #f))]))

(define (meta-expand-once top-level-form)
  ; Partially expands top-level-form and returns a syntax object for 
  ; the partially-expanded expression. Due to limitations in the 
  ; expansion mechanism, some context information may be lost. 
  ; In particular, calling expand-once on the result may produce 
  ; a result that is different from expansion via expand.
  
  ; Before top-level-form is expanded, its lexical context is enriched
  ; with namespace-syntax-introduce, as for eval.
  (meta-expand-syntax-once
   (enrichen-top-level-form top-level-form)))

(define (meta-expand-syntax-once top-level-form)
  ; Like (expand-once stx), except that the argument must be a syntax object, 
  ; and its lexical context is not enriched before expansion.
  (error))

(define (expand-to-top-form top-level-form)
  ; Partially expands top-level-form to reveal the outermost syntactic form. 
  ; This partial expansion is mainly useful for detecting top-level uses of begin. 
  ; Unlike the result of expand-once, expanding the result of expand-to-top-form 
  ; with expand produces the same result as using expand on the original syntax.
  ; Before stx-or-sexpr is expanded, its lexical context is enriched with 
  ; namespace-syntax-introduce, as for eval.
  (meta-expand-syntax-to-top-form
   (enrichen-top-level-form top-level-form)))

(define (meta-expand-syntax-to-top-form top-level-form)
  ; Like (expand-to-top-form stx), except that the argument must be a syntax object, 
  ; and its lexical context is not enriched before expansion.
  (error)
  '(syntax-parse top-level-form
     (match (syntax-e top-level-form)
       [(list '#%expression expr) '...]
       [(list '#%module '...)
        ...])))

(define (syntax: x datum [srcloc #f] [prop #f])
  (cond
    [(and srcloc prop) (datum->syntax x datum srcloc prop)]
    [srcloc            (datum->syntax x datum srcloc x)]
    [else              (datum->syntax x datum x x)]))

; continue : syntax phase environment -> syntax
;   expand x in phase p
(define (continue x p r)
  (trace (list 'continue 'x x))
  (cond
    [(identifier? x) (meta-expand-identifier x p r)]
    [(stx-pair? x)   (define a (stx-car x))
                     (cond [(identifier? a)
                            (define b (or (identifier-binding a p) (lookup r p a)))
                            ;(displayln (list 'continue 'b (~b b)))
                            ; determine binding type
                            (define t (match b
                                        [#f        (top-identifier-type a p)]       ; unbound or top
                                        ['lexical  (lexical-identifier-type r p a)] ; local
                                        [(macro _) b]                      ;  bound by meta expansion
                                        [_         (module-identifier-type a p b)]))
                            (match t
                              ; these handle "real" binding info
                              [(list _ 'kernel) (meta-expand-kernel-application x p r a #f b t)]
                              ['syntax          (meta-expand-macro-application  x p r a #f b t)]
                              [(list value)     (meta-expand-introduce-#%app    x p r)]
                              ; these handle bindings introduced by meta expansion
                              [(macro _)        (meta-expand-macro-application  x p r a #f b t)]
                              [#f (error 'meta-expand "reference to undefined identifier: ~a ~a" a t)]
                              [_ (displayln (list a b t))
                                 (error 'continue "internal error")])]
                           [else ; could be ((foo))
                            (meta-expand-introduce-#%app x p r)])]
    [else            (meta-expand-introduce-#%datum x p r)]))

(define (meta-expand-expression x p r)
  (continue x p r))

(define (meta-expand-bodies xs p r dc)
  ; TODO: Handle definitions
  ; TODO: Handle mix of definitions and expressions
  (for/list ([x (in-list xs)])
    (meta-expand-expression x p r)))

; check-formals : syntax syntax -> (or #f (list identifier))
;   return list of identifiers in formals,
;   return #f if x is not a formals
(define (check-formals x fs)
  (match fs
    [(stx-list (? identifier? id) ...)           id]
    [(? identifier? id)                          (list id)]
    [(stx-list-rest (? identifier? id) ... idn)  (append id (list idn))]
    [_ (raise-syntax-error x "expected formals" x)]))


(define (meta-expand-kernel-application x p r xid id? b t)
  (trace (list 'meta-expand-kernel-application x p r xid id? b t))
  (match-define (list sym 'kernel) t)
  (match sym
    ; TODO : In a module context #%top raises an unbound error (not so in the top-level)
    ['#%top   ; (#%top . id) => i
     (cond [id? (raise-syntax-error "#%top bad syntax")]
           [else (define id (stx-cdr x))
                 (cond #;[(and (identifier? id) (= p 0) (unbound? e 0 id)) 
                          (raise-syntax-error 
                           #f
                           "undefined;\ncannot reference an identifier before its definition" id)]
                       [(identifier? id) id]                       
                       [else (error "bad syntax #%top" x)])])]
    ['#%datum ; (#%datum . d) => (quote d) unless d is a keyword
     (cond [id? (raise-syntax-error "meta: #%datum bad syntax")]
           [else (define d (stx-cdr x))
                 (cond [(keyword? d) (error "#%datum: keyword used as expression")]
                       [else (define q (syntax: x 'quote))
                             (syntax: x (cons q (cons d '())))])])]
    ['#%app   ; (#%app proc-expr arg ...)  Applies a procedure.
     ;        ; this is actually #%plain-app. #%kernel exports it as #%app
     ;        ; TODO: special case: (#%plain-app) expands to '()
     (cond [id? (raise-syntax-error "#%app illegal use")]
           [else (define d (stx-cdr x))
                 (cond [(stx-list? d) (define args (stx->list d))
                                      (define expanded-args (map (λ (a) (continue a p r)) args))
                                      (syntax: x (cons xid expanded-args))]
                       [else (error "application illegal use of .")])])]
    ['let-values ; (let-values ([(id ...) val-expr] ...) body ...+)
     (if id? (raise-syntax-error "let-values illegal use")
         (match x
           [(stx-list l-v (stx-list (stx-list (stx-list idss ...) ves) ...) bs ..1)
            (let* (; expand es in old environment
                   [ves (stx-map (λ (x) (meta-expand-expression x p r)) ves)]
                   ; extend environment (i.e. gived idss lexical bindings)
                   [e* (extend** r p idss (genlab** idss) (genlex** idss))]
                   ; make new definition context
                   ; TODO: (define dc (meta-syntax-local-make-definition-context))
                   [dc 'internal-definition-context]
                   [bs (meta-expand-bodies bs p e* dc)]
                   ; assemble clauses
                   [cs (for/list ([ids (in-list idss)] [ve (in-list ves)])
                         (list ids ve))])
              ; assemble fully expanded let-values
              (syntax: x (list* l-v cs bs)))]
           [_ 
            (error "let-values illegal use")]))]
    ['letrec-values ; (letrec-values ([(id ...) val-expr] ...) body ...+)
     (if id? (raise-syntax-error "letrec-values illegal use")
         (match x
           [(stx-list l-v (stx-list (stx-list (stx-list idss ...) ves) ...) bs ..1)
            (let* (; extend environment (i.e. gived idss lexical bindings)
                   [e* (extend** r p idss 'value)]
                   ; expand es in new environment
                   [ves (stx-map (λ (x) (meta-expand-expression x p e*)) ves)]
                   ; make new definition context
                   ; TODO: (define dc (meta-syntax-local-make-definition-context))
                   [dc 'internal-definition-context]
                   [bs (meta-expand-bodies bs p e* dc)]
                   ; assemble clauses
                   [cs (for/list ([ids (in-list idss)] [ve (in-list ves)])
                         (list ids ve))])
              ; assemble fully expanded let-values
              (syntax: x (list* l-v cs bs)))]
           [_ 
            (error "letrec-values illegal use")]))]
    ['define-values ; (define-values (id ...) expr)
     (if id? (raise-syntax-error "define-values illegal use")
         (match x
           [(stx-list d-v (stx-list ids ...) expr)
            (let* (; extend environment
                   [e* (extend* r p ids (genlab* ids) (genlex* ids))]
                   ; expand expr in new environment
                   [v (meta-expand-expression expr p e*)])
              ; assemble fully expanded define-values
              (syntax: x (list d-v ids v)))]
           [_ 
            (displayln x)
            (error "define-values illegal use")]))]
    ['set! ; (set! id expr)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list s! id expr)
            (unless (identifier? id) (raise-syntax-error 'set! "not an identifier" id))
            (let* ([expr (meta-expand-expression expr p r)])
              (syntax: x (list s! id expr)))]
           [_ (raise-syntax-error 'set! "bad syntax" x)]))]
    ['if ; (if expr expr expr)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list i e0 e1 e2)
            (let* ([e0 (meta-expand-expression e0 p r)]
                   [e1 (meta-expand-expression e1 p r)]
                   [e2 (meta-expand-expression e2 p r)])
              (syntax: x (list i e0 e1 e2)))]
           [_ (raise-syntax-error 'if "bad syntax" x)]))]
    ['begin ; (begin expr ..+)
     ; TODO: top-level begins are in separate definition contexts
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list beg es ..1)
            (let* ([es (for/list ([e0 (in-list es)])
                         (meta-expand-expression e0 p r))])
              (syntax: x (list* beg es)))]
           [_ (raise-syntax-error 'begin "bad syntax" x)]))]
    ['begin0 ; (begin0 expr expr ...)
     ; TODO: top-level begins are in separate definition contexts
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list beg0 es ..1)
            (let* ([es (for/list ([e0 (in-list es)])
                         (meta-expand-expression e0 p r))])
              (syntax: x (list* beg0 es)))]
           [_ (raise-syntax-error 'begin0 "bad syntax" x)]))]
    ['#%expression ; (#%expression expr)
     ; TODO: (meta-expand '(or 4 5)) wraps '5 in (#%expression _), expand doesn't. Why?
     ; Because: If a macro transformer returns (#%expression e) into a 
     ; a context known to be an expression context, the #%expression needs to be discarded.
     ; (The point of #%expression is to force an expression context, where there is doubt.)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list ex e0)
            (displayln "--#%expression--")
            (let ([e0 (meta-expand-expression e0 p r)])
              (match e0
                [(stx-cons (<#%expression>) _) (syntax: x e0)]              ; don't repeat
                [_                             (syntax: x (list ex e0))]))] ; common case
           [_ (raise-syntax-error '#%expression "bad syntax" x)]))]
    ['quote ; (quote datum)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list q d)
            ; remove all lexical context from datum
            (syntax: x (list q (strip-context d)))]
           [_ (raise-syntax-error 'quote "bad syntax" x)]))]
    ['quote-syntax ; (quote-syntax datum)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list sq d)
            ; keep lexical context from datum
            (syntax: x (list sq d))]
           [_ (raise-syntax-error 'syntax-quote "bad syntax" x)]))]
    ['with-continuation-mark ; (with-continuation-mark expr expr expr)
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list wcm e0 e1 e2)
            (let* ([e0 (meta-expand-expression e0 p r)]
                   [e1 (meta-expand-expression e1 p r)]
                   [e2 (meta-expand-expression e2 p r)])
              (syntax: x (list wcm e0 e1 e2)))]
           [_ (raise-syntax-error 'with-continuation-mark "bad syntax" x)]))]
    ['#%variable-reference 
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list vr) x]
           [(or (stx-list vr                     (? identifier? id))
                (stx-list vr (stx-cons (<#%top>) (? identifier? id))))
            x]
           [_ (raise-syntax-error '#%variable-reference "bad syntax" x)]))]
    ['lambda  ; (#%plain-lambda formals body ...+)
     ;        ;  #%plain-lambda is exported as lambda by #%kernel
     (displayln "XXXXXXXXX")
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list pl formals bs ..1)
            (define ids (check-formals x formals))
            (let* (; extend environment (i.e. gived idss lexical bindings)
                   [e* (extend* r p ids (genlab* ids) (genlex* ids))]
                   ; expand body ... in new environment                   
                   ; TODO: (define dc (meta-syntax-local-make-definition-context))
                   ; make new definition context
                   [dc 'internal-definition-context]
                   [bs (meta-expand-bodies bs p e* dc)])
              (syntax: x (list* pl formals bs)))]
           [_ (raise-syntax-error '#%plain-lambda "bad syntax" x)]))]
    ['case-lambda  ; (case-lambda [formals body ...+)] ...
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list cl (stx-list formalss bss ..1) ...)
            (define idss (for/list ([formals (in-list formalss)])
                           (check-formals x formals)))
            (define cases
              (for/list ([ids (in-list idss)] [bs (in-list bss)])
                (let* (; extend environment (i.e. gived ids lexical bindings)
                       [e* (extend* r p ids 'value)]
                       ; expand body ... in new environment
                       ; TODO: (define dc (meta-syntax-local-make-definition-context))
                       ; make new definition context
                       [dc 'internal-definition-context]
                       [bs (meta-expand-bodies bs p e* dc)])
                  (list ids bs))))
            (syntax: x (list* cl cases))]
           [_ (raise-syntax-error '#%plain-lambda "bad syntax" x)]))]
    ['letrec-syntaxes+values
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list lsv 
                      (stx-list (stx-list (stx-list trans-idss ...) trans-exprs) ...)
                      (stx-list (stx-list (stx-list   val-idss ...)   val-exprs) ...)
                      bs ..1)
            (let*  ; TODO: rename ids in trans-idss and val-idds per paper
                (; expand the transformer expressions in an empty environment
                 ; Note: Racket specifies an empty environment
                 [tes (for/list ([te (in-list trans-exprs)])
                        (meta-expand-expression te p empty-environment))]
                 ; evaluate the (fully) expanded expressions
                 [tes-vals (for/list ([te (in-list trans-exprs)])
                             (call-with-values (λ () (eval te)) list))]
                 [*_* (displayln (list 'trans-exprs trans-exprs
                                       'tes tes
                                       'tes-vals tes-vals))]
                 ; bind idss lexically and trans-ids to syntax
                 [r* (extend** r  p   val-idss (genlab**   val-idss) (genlex**   val-idss))]
                 [r* (extend** r* p trans-idss (genlab** trans-idss) (genmac** trans-idss tes-vals))]
                 ; expand value expressions in an environment where val-idss and trans-idss are bound
                 [val-exprs (for/list ([ve (in-list val-exprs)])
                              (meta-expand-expression ve p r*))]
                 ; TODO: (define dc (meta-syntax-local-make-definition-context))
                 ; make new definition context 
                 [dc 'internal-definition-context]
                 [bs (meta-expand-bodies bs p r* dc)])
              ; the transformer clauses are discarded and the form reduces 
              ; to "a combination of letrec-values or let-values"
              (match val-idss
                ['()  (syntax: x (list* #'let-values '() bs))]
                [_    (syntax: x (list* #'letrec-values 
                                        (map list val-idss val-exprs)
                                        bs))]))]
           [_ (raise-syntax-error 'letrec-syntaxes+values "bad syntax" x)]))]
    ['begin-for-syntax
     (if id? (raise-syntax-error #f "bad syntax" xid)
         (match x
           [(stx-list bfs forms ...)
            (syntax: x (list* bfs (for/list ([x forms])
                                    (meta-expand-top-form x (+ p 1) r))))]
           [_ (raise-syntax-error 'begin-for-syntax "bad syntax" x)]))]
    [(? (λ (_) (kernel-form-identifier? xid)))
     (displayln x)
     (error)] ; implement it!     
    ; XXX we now need to now if it is bound to syntax ...
    [(? (λ(_) id?)) x] ; reference to   module-level id
    [else              ; application of module-level id
     (meta-expand-introduce-#%app x p r)]))

(define (meta-expand-top-form x p r)
  (continue x p r))

; meta-expand-module-application : syntax phase env identifier boolean binding binding-type -> syntax
;  xid is a module bound identifier (and not from #%kernel)
;  id? = #t means x is an identifier  (and x and xid are eq?)
;  id? = #f means x has the form (xid . _) where xid is an identifier
;  b   = output from identifier-binding
;  t   = output from module-identifier-type
;        or #f  (in which case module-identifier-type is called here)
(define (meta-expand-module-application x p r xid id? b t)
  (trace (list 'meta-expand-module-application x p r xid id? b t))
  (match (or t (module-identifier-type xid p b))
    ['syntax         (meta-expand-macro-application x p r xid id? b t)] ; macro
    [(? (λ(_) id?))  xid]                                               ; reference
    [_               (meta-expand-introduce-#%app x p r)]))             ; application

; meta-expand-macro-application : syntax phase env identifier boolean -> syntax
;  xid is an identifier bound to syntax
;  id? = #t means x is an identifier  (and x and xid are eq?)
;  id? = #f means x has the form (xid . _) where xid is an identifier
;  b   = output from identifier-binding
;  t   - output from *-identifier-type
(define (meta-expand-macro-application x p r xid id? b t)
  (trace (list 'meta-expand-macro-application x p r xid id? b t))
  ; TODO: handle identifier-macros, set!-macros and rename-macros (more?)
  ; TODO: install parameters for syntax-transforming? , syntax-local- ...
  ; TODO: check that output from T is syntax
  ; TODO: merge syntax properties : see 12.7 in the reference
  ; TODO: use syntax-track-origin
  
  ; Since this is a meta-expander we have two types of macros to handle:
  ;     i) introduced by meta-expansion
  ;    ii) introduced by real expansion
  (define type (match b [(macro _) 'meta] [_ 'real]))
  ; In both cases we need to get the transformer T associated with the binding.  
  (define T
    (let loop ([b b])
      (match b
        [(macro (? procedure? transformer)) transformer]             ; ad  i)
        [(macro (? rename-transformer? rt)) 
         (loop (lookup r p (rename-transformer-target rt)))]
        [_ (syntax-value xid p)])))                                  ; ad ii)
  
  (unless (procedure? T)
    (displayln (list 'T: T))
    (error "bad use of syntax in:" x))
  
  (define m (make-syntax-introducer))                ; get new mark m
  (define mx (m x))                                  ; apply it to input syntax
  (displayln (list 'here: T mx))
  (define Tmx                                        ; apply transformer    
    (match type
      ['meta (T mx)]
      ['real (call-transformer T mx 'expression)]))
  (define out (m Tmx))                             ; mark again
  (displayln (list 'macro: 'in xid 'out out))
  (continue out p r))         ; apply mark before and after application of transformer



(define (call-transformer T mx context) ; mx is already marked
  ; Conceptually just (call-transformer T mx) == (T mx)
  ; However to support calling real Racket transformer,
  ; some of them use syntax-local- constructs, that throws
  ; exn:fail if called while not transforming (using the real expander).
  ; Here we try if (T mx) works, and if it does fine.
  ; If an exception is thrown, we attempt to emulate transforming
  ; by calling fake-transform.
  (with-handlers ([syntax-local-exn? 
                   (λ (_) (fake-transform T mx context))])
    (T mx)))

; syntax-local-exn? : exception -> boolean
;   was the exception thrown by a syntax-local- construct?
(define (syntax-local-exn? e)
  (and (exn:fail? e)
       (regexp-match #rx"^syntax-local-.*" (exn-message e))))

; fake-transform : transformer syntax context
;   call the transformer T on x in the given local context
(define (fake-transform T x context)
  (trace (list 'fake-transform T x context))
  ; this call the transformer T in an expression context
  (match context
    ['expression (define out (let/ec return
                               (eval `(let-syntax ([m (λ(_) (,return (,T #',x)))]) (m)))))
                 (displayln out)
                 out]
    [_ (error)])) ; todo

(define (meta-expand-identifier x p r)
  (trace (list 'meta-expand-identifier x p r))
  (define b (identifier-binding x p))
  (match b
    [#f        ; reference to top-level or unbound
     (meta-expand-introduce-#%top x p r)]
    ['lexical
     (meta-expand-nontop-binding x p r b x #t)]
    [_         ; module 
     (meta-expand-module-application x p r x #t b #f)]))


; meta-expand-nontop-binding : syntax phase env binding boolean -> syntax
;   id? = #t  means x is an identifier, #f means (cons xid . _)
;   binding info in b stems from (identifier-binding x) or (identifier-binding xid)
;   if x is an identifier, pass xid and x should be eq?
(define (meta-expand-nontop-binding x p r b xid id?)
  ; (trace (list 'meta-expand-nontop-binding x p e (~b b) xid id?))
  (trace (list 'meta-expand-nontop-binding x))
  (match b
    ['syntax  ; xid is bound to a syntax
     (meta-expand-macro-application x p r xid id?)]
    ['lexical ; a lexical binding (e.g. bound by let or define)
     (if id?
         xid  ; variable reference
         (meta-expand-introduce-#%app x p))]
    ; module bound
    [(list nom-mpi nom-sym src-mpi src-sym src-p in-p nom-ex-p)
     (cond
       ; (#%top . id) => id
       [(bound-identifier=? xid #'#%top)
        (cond [id? (raise-syntax-error "#%top bad syntax")]
              [else (define id (stx-cdr x))
                    (cond [(identifier? id) id]
                          [else (error "bad syntax #%top" x)])])]
       ; (#%datum . d) => (quote d) unless d is a keyword
       [(bound-identifier=? xid #'#%datum)
        (cond [id? (raise-syntax-error "#%datum bad syntax")]
              [else (define d (stx-cdr x))
                    (cond [(keyword? d) (error "#%datum: keyword used as expression")]
                          [else (define q (syntax: x 'quote))
                                (syntax: x (cons q (cons d '())))])])]
       ; (#%app proc-expr arg ...)  Applies a procedure.
       [(bound-identifier=? xid #'#%app)
        (cond [id? (raise-syntax-error "#%app illegal use")]
              [else (define d (stx-cdr x))
                    (cond [(stx-list? d) (define args (stx->list d))
                                         (define expanded-args (map (λ (a) (continue a p r)) args))
                                         (syntax: x (cons xid expanded-args))]
                          [else (error "application illegal use of .")])])]
       ; 
       #;(with-namespace (module->namespace mpi)
           (with-handlers ([exn:fail:syntax? (λ (e) 'syntax)])
             (namespace-variable-value 'let)))
       ; raises an exception for #%kernel
       #;(with-namespace (module->namespace (first (identifier-binding #'map)))
           (with-handlers ([exn:fail:syntax?            (λ (e) 'syntax)]
                           [exn:fail:contract:variable? (λ (e) 'unbound)])
             (namespace-variable-value 'map #t)))
       
       ; XXX we now need to now if it is bound to syntax ...
       [id? x] ; reference to module-level id
       [else   ; application of module-level id
        (meta-expand-introduce-#%app x p r)])]
    [_ (error)]))


(define (meta-expand-introduce-#%top x p r)
  (trace (list 'meta-expand-introduce-#%top x p r))
  ; note: top is usually bound to the #%top from #%kernel
  ; create new #%top symbol with lexical info from x
  (define top (syntax: x '#%top))
  ; if #%app is bound, expand (#%app . x)
  (if (unbound? r p top)
      (raise (exn:fail:syntax "no #%top bound"  (current-continuation-marks) (list x)))
      (continue (syntax: x (cons top x)) p r)))

(define (meta-expand-introduce-#%app x p r)
  (trace (list 'meta-expand-introduce-#%app x p r))  
  ; create new #%app symbol with lexical info from x
  (define app (syntax: x '#%app))
  ; if #%app is bound, expand (#%app . x)
  (if (unbound? r p app)
      (raise (exn:fail:syntax "no #%app bound"  (current-continuation-marks) (list x)))
      (continue (syntax: x (cons app x)) p r)))

(define (meta-expand-introduce-#%datum x p r)
  (trace (list 'meta-expand-introduce-#%datum x p r))
  ; note #%datum is usually bound to a syntax transformer that
  ; expands (#%datum . d) to 'd
  (define datum (syntax: x '#%datum))
  (cond [(unbound? r p datum)
         (raise (exn:fail:syntax "no #%datum bound"  (current-continuation-marks) (list x)))]
        [(eq? (syntax-e x) '())
         (raise (exn:fail:syntax "#%app: missing procedure expression" 
                                 (current-continuation-marks) (list x)))]
        [else
         (continue (syntax: x (cons datum x)) p r)]))


;;;
;;; FORMATTING
;;;

(define (~b b)  ; ~b for binding
  (cond 
    [(list? b) (map ~mpi b)]
    [else (error)]))

(define (~mpi x)
  (define (resolve mpi) (resolve-module-path-index mpi (string->path "xxx")))
  (if (module-path-index? x)
      (resolve x)
      (~a x)))

; ~id : syntax phase -> string
(define (~id s [p 0])
  (define (resolve mpi) (resolve-module-path-index mpi (string->path "xxx")))
  (list (syntax-e s)
        (match (identifier-binding s p)
          ; #f = top-level or unbound
          [(and it (or #f 'lexical)) it]
          ; module binding
          [(and it (list src-mpi src-sym nom-mpi nom-sym src-phase import-phase nom-export-phase))
           (map (λ(x) (apply-when module-path-index? resolve x)) it)])))

;;;
;;; LOCAL-EVAL
;;;

; Local evaluation of expressions are needed to evaluate the right hand side of a let-syntax.

; local-eval : full-expanded-expression namespace environment -> values
;   evaluate the expression x (a syntax-object representing af fully-expanded expression)
;   where local variable references are resolved in the environment r
;   and   global variable references in the namespace ns.


; An environment:
(struct env (bindings parent))
; parent = #f is no parent
; bindings is a list of:
; (struct binding (label phase type value) #:mutable)
; label is a symbol (from identifier-binding-symbol)
; if type is 'lexical, then value is either a box or #f

(define empty-env (env '() #f))
(define (make-lexical-binding l p v)
  (binding l p 'lexical (box v)))
(define undefined (list 'undefined))
(define (undefined? o) (eq? o undefined))
;(define (add-lexical-binding r l [v undefined]) 'todo)
(define (lexical-store*) 'todo)  


#;(define (local-eval x r [ns (current-namespace)])
    (define id? identifier?)
    (define (lookup x r [ns (current-namespace)]) (error))
    (define (set r ns id v) (error))
    (define (ev* es r) ; es is a non-empty list of expressions
      (match es
        [(list e)      (ev e r)]
        [(list* e0 es) (ev e0 r) 
                       (ev* es r)]))
    (define (formals-ids fs)
      (match fs
        [(stx-list      ids ...)     ids]
        [(stx-list-rest ids ... idn) (append ids (list idn))]
        [(? id? id)                  (list id)]
        [_                           (error)]))
    (define (ev x r)
      (match x
        [(? identifier?)                 (lookup x r)]
        [(stx-list (<if>) e0 e1 e2)      (if (ev e0 r) (ev e1 r) (ev e2 r))]
        [(stx-list (<begin>) es ... en)  (for ([e (in-list es)]) (ev e r))
                                         (ev en r)]
        [(stx-list (<begin0>) e)         (ev e r)]
        [(stx-list (<begin0>) e0 es ...) (define vs (call-with-values (λ() (ev e0 r)) list))
                                         (for ([e (in-list es)]) (ev e r))
                                         (apply values vs)]
        [(stx-list (<let-values>) (stx-list [stx-list (stx-list idss) ces] ...) es ..1)
         (define vss (for/list ([ce (in-list ces)]) (call-with-values (λ() (ev ce r)) list)))
         (ev* es (extend** r idss vss))]
        [(stx-list (<letrec-values>) (stx-list [stx-list (stx-list idss) ces] ...) es ..1)
         (define undefss (for/list ([ids (in-list idss)]) (for/list ([id (in-list ids)]) 'undefined)))
         (define r* (extend** r idss undefss))
         (for/list ([ids (in-list idss)] [ce (in-list ces)])
           (define vs (call-with-values (λ() (ev ce r)) list))
           (lexical-store* r* ids vs))
         (ev* es r*)]
        [(stx-list (<set!>) (? id? id) e) 
         (set r ns id (ev e r))]
        [(stx-list (<quote>) d)
         d]
        [(stx-list (<quote-syntax>) d)
         d]
        [(stx-list (<with-continuation-mark>) e0 e1 e2)
         (with-continuation-mark (ev e0 r) (ev e1 r) (ev e2 r))]
        [(stx-list (<#%plain-app>) e0 es ...)
         (apply (ev e0 r) (for/list ([e (in-list es)]) (ev e r)))]
        [(stx-cons (<#%top>) (? id? id))
         (namespace-variable-value (identifier-binding-symbol id))]
        [(stx-list (<#%variable-reference>) (? id? id))
         (eval `(#%variable-reference ,id))]
        [(stx-list (<#%variable-reference>) (stx-cons (<#%top>) (? id? id)))
         (eval `(#%variable-reference (#%top ,id)))]
        [(stx-list (<#%variable-reference>))
         (eval `(#%variable-reference))]
        [(stx-list (<#%plain-lambda>) formals e)
         (define ids (formals-ids formals))
         (define closed (λ (vals) (ev e (extend* r ids vals))))
         (eval `(lambda ,formals (,ev ,@ids)))]
        [_ ; catch forms not yet implemented
         (error)]))
    (ev x r))






;;;
;;; TEST
;;;

(displayln (with-namespace namespace-here (expand '(#%top . x))))

(with-namespace namespace-here
  (list
   (and (free-identifier=?  (meta-expand 'x) (expand 'x))
        (bound-identifier=? (meta-expand 'x) (expand 'x)))
   (let ([y 2]) 
     (and (free-identifier=?  (meta-expand 'x) (expand 'x))
          (bound-identifier=? (meta-expand 'x) (expand 'x))))))

(with-namespace namespace-here
  (meta-expand '(+  1 2)))

; (meta-expand #'(letrec-syntaxes+values ([(m) (#%plain-lambda (_) #'42)]) () (m)))

