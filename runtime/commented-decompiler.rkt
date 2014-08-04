#lang racket/base
;;; Copy of compiler-pkgs/compiler-lib/compiler/decompile.rkt
;;; July 17th 2014 - 83a573ccd8b216d9600435692dfa4da851a55d91

;;; Goal: Understand how bytecodes work in Racket.

(require compiler/zo-parse        ; parses bytecode to zo structures that represents bytecode
         compiler/zo-marshal      ; converts zo structures to bytecode
         syntax/modcollapse       ; used to simplify module paths         
         racket/port racket/match ; standard racket libraries
         racket/list racket/set 
         racket/path racket/fasl
         racket/format)
;;;
;;; Overview
;;;

;          read       compile                        zo-parse
;  string   ->   sexp   ->     bytecode   ->   bytes   ->       zo-struct

; To produce bytecode for a program, the program needs to be read and compiled.
; The procedures to are named  read  and  compile.
; Reading is simple enough, but preparation is need to use the compile procecure.
; The compiler needs a context to determine the meaning of identifiers.
; The compile procedure use the current namespace as this context.
; To compile "(+ 1 2)" in a context where the identifier + is associated to the
; primitive that performs addition, one must set up a name space and 
; import the primitives (most of which are in the #%kernel module).

(define (string->bytecode str)
  (define ns (make-base-empty-namespace))
  (parameterize ([current-namespace ns])
    (namespace-require ''#%kernel)
    (namespace-require 'racket/base)
    (define in       (open-input-string str))  ; convert string to port
    (define s-exp    (read in))                ; read
    (define bytecode (compile s-exp))          ; compile
    bytecode))

; The actual bytecode looks something like this:  #~6.0.1.13T ...gibberish...
; The #~ indicates it is bytecode. The 6.0.1.13 is the version of Racket
; used to produce the bytecode and then random characters are displayed.

; In order to examine the bytecode we need to parse into a more human readable format.
; The module compiler/zo-parse contains a parser that parses byte strings containing
; bytecode in to zo-structures. The name zo doesn't mean anything. It is an
; old pun and stands for Zodiac. Here zo structures simply represents bytecode
; as structures.

; string->zo : string -> zo
(define (string->zo str)
  (define bytecode (string->bytecode str))                         ; compile to bytecode
  (define bs       (with-output-to-bytes (λ () (write bytecode)))) ; convert to bytestring
  (define zo       (zo-parse (open-input-bytes bs)))               ; parse to zo structs
  zo)

;;; Example

; > (string->zo "(+ 1 2)")
; '#s((compilation-top zo 0) 0 #s((prefix zo 0) 0 () ()) 3)

; As written it looks a little odd. Normally we write:
;   (compilation-top0 (prefix 0 '() '()) 3)

; Here the #s stands for (prefrabricated) structure, which means the system 
; can read and write the structures produced by zo-parse.

; Rather than just compilation-top we see (compilation-top zo 0). 
; It simply means that compilation-top has a zo structure as a super type.
; Note that the zo structure has no fields. 

; Back to the result of compiling (+ 1 2):
;   (compilation-top0 (prefix 0 '() '()) 3)
; Where did the +, 1 and 2 go? 
; Well, the compiler determined at compile time that (+ 1 2) gives 3,
; so the actual bytecode consists of nothing else but the constant 3.

;;; Exercise
; Find a small program which forces the runtime to perform the calcuation (+ 1 2).
; This attempt failed:
;   > (string->zo "((lambda (x) (+ 1 x)) 2)")
;   '#s((compilation-top zo 0) 0 #s((prefix zo 0) 0 () ()) 3)

;;;
;;; Running bytecode representing zo structures
;;;

(define (eval-zo zo)
  (fasl->s-exp 
   (open-input-bytes 
    (zo-marshal zo))))

; In order to run code represented as zo-structures it must be converted to bytecode.
;  (define bs (zo-marshal (string->zo "(begin (define x 1) x)"))) ; a bytestring of bytecode
;  (fasl->s-exp bs) ; evaluates the bytecode

; The following example evaluates to 120.
#;(fasl->s-exp 
   (open-input-bytes 
    (zo-marshal 
     (string->zo 
      (~a '(let ()
             (define (fact n)
               (if (zero? n)
                   1
                   (* n (fact (- n 1)))))
             (fact 5)))))))

;;;
;;; Decompilation
;;;

(provide decompile)  ;  decompile: zo-struct -> s-exp

; This module implements the decompile function, which converts
; the often hard to read zo-structures into a more readable s-exp format.
; The output of decompile is not meant to be executable. 
; The decompiler is mostly useful for examining bytecode, for example
; to debug the compiler or to see how which optimizations the compiler
; performs.

;;; 
;;; Primitives
;;;

; Procedures implemented in the C runtime are called primitives.
; In bytecode they are referred to by index (number). 
; In the output of the decompiler we like to see actual names,
; so we need a table that maps the index to a name. 
; Introducing new or removing old primitives can change their index, 
; so to avoid changing the table of primitives manually, we do the 
; following:
;   -  make a namespace and import all primitives into it 
;      by requiring #%kernel, #%unsafe, etc.
;   - for each identifier in the name space, compile a reference to it
;   - see if the result contains (struct primval (n)) 
;   - if so the index is n, if not the identifier wasn't bound to a primitive

; The result is a table of the form:
; '#hash((665 . date-time-zone-offset) (794 . exn:fail:contract:divide-by-zero) ...)

(define primitive-table  ; hashtable from index to symbol
  (let ([bindings
         (let ([ns (make-base-empty-namespace)])           ; make namespace with racket/base attached
           (parameterize ([current-namespace ns])
             (namespace-require ''#%kernel)                ; import all primitives
             (namespace-require ''#%unsafe)
             (namespace-require ''#%flfxnum)
             (namespace-require ''#%extfl)
             (namespace-require ''#%futures)
             (namespace-require ''#%foreign)        
             (for/list ([l (namespace-mapped-symbols)])    ; compile a reference to each symbol
               (cons l (with-handlers ([exn:fail? (lambda (x) #f)])
                         (compile l))))))]
        [table (make-hash)])
    (for ([b (in-list bindings)])
      (let ([v (and (cdr b)
                    (zo-parse                              ; parse the bytecode to zo structures
                     (open-input-bytes
                      (with-output-to-bytes
                          (λ () (write (cdr b)))))))])
        (let ([n (match v                                  ; is it a reference to a primitive?
                   [(struct compilation-top (_ prefix (struct primval (n)))) n]
                   [else #f])])
          (hash-set! table n (car b)))))                   ; if so, add it to the table
    table))

(define (list-ref/protect l pos who)                       
  ; useful for debugging faulty bytecode ...
  (list-ref l pos)
  #;
  (if (pos . < . (length l))
      (list-ref l pos)
      `(OUT-OF-BOUNDS ,who ,pos ,(length l) ,l)))

;;;
;;; Decompilation
;;;

; The function zo-parse will parse bytecode and deliver zo-structures
; representing the bytecode in all detail. The function decompile 
; converts this structure into a human readable s-exp.

; The code is written as a recursive descent. To pass along information
; on globally defined variables, the structure glob-desc is used.

(define-struct glob-desc (vars num-tls num-stxs num-lifts))  ; explanation follows
; (num-tls stands for "number of toplevels)

; The result of zo-parse is a compilation-top, so that's where the
; decompilation process begins.

; (struct compilation-top zo (max-let-depth prefix code)

; The compilation-top consists of code, which are instructions to run on a stack machine.
; The max-let-depth is maximum stack depth that code creates (not counting the prefix array).
; The prefix describes what the runtime must push on the stack before executing code.

(define (decompile top)
  (let ([stx-ht (make-hasheq)]) ; hashtable from wraped syntax objects to decompiled ones
    (match top
      [(struct compilation-top (max-let-depth prefix form)) ; form represents the code to run
       ; decompile-prefix returns a description of the global variables
       ; and a list of definition that represents ... TODO ...
       (let-values ([(globs defns) (decompile-prefix prefix stx-ht)])
         `(begin
            ,@defns
            ,(decompile-form form globs '(#%globals) (make-hasheq) stx-ht)))]
      [else (error 'decompile "unrecognized: ~e" top)])))

; (struct prefix zo (num-lifts toplevels stxs)
; A prefix is an array holding variables. 
; The array is pushed to the stack to initiate evaluation.

; Each slot of the array is called a bucket.
; The buckets are used in this order:
;     toplevels, stxs, maybe one extra bucket, lifted-local-procedures
; The extra bucket is only used if stxs is non-empty.
;   The number of buckets used for  toplevels      are  (length toplevels)
;   The number of buckets used for  stxs           are  (length stxs)
;   The number of                   extra buckets  are  (if (empty? stxs) 0 1)
;   The number of         lifted-local-procedures  are  num-lifts.
; The length of the array are thus known.

(define (decompile-prefix a-prefix stx-ht)
  (match a-prefix
    [(struct prefix (num-lifts toplevels stxs))
     (let ([lift-ids (for/list ([i (in-range num-lifts)])  ; give symbols to local procedures
                       (gensym 'lift))]                    
           [stx-ids (map (lambda (i) (gensym 'stx))        ; give symbols to stxs
                         stxs)])
       ; Remember: (define-struct glob-desc (vars num-tls num-stxs num-lifts))
       (values (glob-desc 
                ; vars = ...
                (append 
                 (map (lambda (tl)
                        (match tl
                          ; #f represents a dummy variable used to access the enclosing module
                          [#f '#%linkage]  
                          ; a symbol is a reference to a variable defined in an enclosing module
                          [(? symbol?) (string->symbol (format "_~a" tl))]
                          ; top-level variables (appears outside of modules)
                          [(struct global-bucket (name)) 
                           (string->symbol (format "_~a" name))]
                          ; variable imported from another module
                          [(struct module-variable (modidx sym pos phase constantness))
                           (if (and (module-path-index? modidx)
                                    (let-values ([(n b) (module-path-index-split modidx)])
                                      (and (not n) (not b)))) ; n = b = #f represents "self module"
                               (string->symbol (format "_~a" sym))  ; identifier from this module
                               (string->symbol 
                                (format "_~s~a@~s~a" ; imported 
                                        sym 
                                        (match constantness
                                          ['constant ":c"] ; same for every instantiation of its mod
                                          ['fixed ":f"]   ; same in a particular module instantiation
                                          [(function-shape a pm?) ; a function
                                           (if pm? ":P" ":p")]    ; :P = preserves continuation marks
                                          [(struct-type-shape c) ":t"]  
                                          [(constructor-shape a) ":mk"] ; (constructor = make = mk)
                                          [(predicate-shape) ":?"]
                                          [(accessor-shape c) ":ref"]
                                          [(mutator-shape c) ":set!"]
                                          [else ""])
                                        (mpi->string modidx)            ; module name 
                                        (if (zero? phase)               ; maybe append phase
                                            ""
                                            (format "/~a" phase)))))]
                          [else (error 'decompile-prefix "bad toplevel: ~e" tl)]))
                      toplevels)
                 stx-ids
                 (if (null? stx-ids) null '(#%stx-array))
                 lift-ids)
                ; num-tls = 
                (length toplevels)
                ; num-stxs =
                (length stxs)
                ; num-lifts =
                num-lifts)
               (map (lambda (stx id)   ; we will ignore stxs for the time being
                      `(define ,id ,(if stx
                                        `(#%decode-syntax 
                                          ,(decompile-stx (stx-encoded stx) stx-ht))
                                        #f)))
                    stxs stx-ids)))]
    [else (error 'decompile-prefix "huh?: ~e" a-prefix)]))

; The function decompile-stx transforms the representation of syntax-objects
; used by zo-parse to mutable lists that besides the syntax object also
; shows lexical information.
;     > (decompile-stx (wrapped #'(a b c) '() 'clean) (make-hash))
;     (mcons 'wrap (mcons #<syntax: (a b c)> '()))
(define (decompile-stx stx stx-ht)
  (or (hash-ref stx-ht stx #f)
      (let ([p (mcons #f #f)])
        (hash-set! stx-ht stx p)
        (match stx
          [(wrapped datum wraps tamper-status)
           (set-mcar! p (case tamper-status
                          [(clean) 'wrap]
                          [(tainted) 'wrap-tainted]
                          [(armed) 'wrap-armed]))
           (set-mcdr! p (mcons
                         (cond
                           [(pair? datum) 
                            (cons (decompile-stx (car datum) stx-ht)
                                  (let loop ([l (cdr datum)])
                                    (cond
                                      [(null? l) null]
                                      [(pair? l)
                                       (cons (decompile-stx (car l) stx-ht)
                                             (loop (cdr l)))]
                                      [else
                                       (decompile-stx l stx-ht)])))]
                           [(vector? datum)
                            (for/vector ([e (in-vector datum)])
                              (decompile-stx e stx-ht))]
                           [(box? datum)
                            (box (decompile-stx (unbox datum) stx-ht))]
                           [else datum])
                         (let loop ([wraps wraps])
                           (cond
                             [(null? wraps) null]
                             [else
                              (or (hash-ref stx-ht wraps #f)
                                  (let ([p (mcons #f #f)])
                                    (hash-set! stx-ht wraps p)
                                    (set-mcar! p (decompile-wrap (car wraps) stx-ht))
                                    (set-mcdr! p (loop (cdr wraps)))
                                    p))]))))
           p]))))

(define (decompile-wrap w stx-ht)
  (or (hash-ref stx-ht w #f)
      (let ([v (match w
                 [(lexical-rename has-free-id-renames?
                                  ignored
                                  alist)
                  `(,(if has-free-id-renames? 'lexical/free-id=? 'lexical) . ,alist)]
                 [(phase-shift amt src dest cancel-id)
                  `(phase-shift ,amt ,src ,dest, cancel-id)]
                 [(wrap-mark val)
                  val]
                 [(prune sym)
                  `(prune ,sym)]
                 [(module-rename phase kind set-id unmarshals renames mark-renames plus-kern?)
                  `(module-rename ,phase ,kind ,set-id ,unmarshals ,renames ,mark-renames ,plus-kern?)]
                 [(top-level-rename flag)
                  `(top-level-rename ,flag)]
                 [else w])])
        (hash-set! stx-ht w v)
        v)))

(define (mpi->string modidx)
  (cond
    [(symbol? modidx) modidx]
    [else 
     (collapse-module-path-index modidx (build-path
                                         (or (current-load-relative-directory)
                                             (current-directory))
                                         "here.rkt"))]))

; (struct mod (name srcname ...))
;   Represents a module declaration.

;> (decompile (string->zo "(module foo racket (+ 1 2))"))
;'(begin
;   (module foo ....
;     (require (lib "racket/main.rkt"))
;     (module configure-runtime ....
;       (require '#%kernel (lib "racket/runtime-config.rkt"))
;       (|_configure:p@(lib "racket/runtime-config.rkt")| '#f))
;     (#%apply-values |_print-values:p@(lib "racket/private/modbeg.rkt")| '3)))

(define (decompile-module mod-form orig-stack stx-ht mod-name)
  (match mod-form
    [(struct mod (name        ; symbol          => module name 
                  ;           ; list of symbols => submodule , '(foo bar) is submodule bar inside foo
                  srcname     ; symbol e.g. bar  for the submodule bar in foo
                  self-modidx ; the module path index
                  prefix      ; a prefix pushed before evaluation of the body
                  provides    ; association list from phases to exports
                  requires    ; association list from phases to imports
                  body        ; code for phase 0
                  syntax-bodies ; syntax-bodies use their own prefix
                  unexported  ; list of lists of symbols, for unexported definitions
                  ;           ; these can be accessed during macro expansion
                  max-let-depth ; max stack depth created by body forms (not counting prefix)
                  dummy       ; access to the top-level namespace
                  lang-info   ; optional module-path for info (used by module->lang-info)
                  internal-context ; internal-module-context lexical context of the body
                  ;                ; #t #f stx or vector of stx
                  flags       ; list of symbols, there 'cross-phase indicates the module-body
                  ;           ; is evaluated once and results shared across all phases
                  pre-submodules  ; module declared submodules
                  post-submodules ; module* declared submodules
                  ))
     (let-values ([(globs defns) (decompile-prefix prefix stx-ht)]
                  [(stack) (append '(#%modvars) orig-stack)]   
                  ; a module declaration pushes an array on stack containing
                  ; the module variables so '#%modvars is consed to the stack as a place holder
                  [(closed) (make-hasheq)]) ; 
       `(,mod-name ,(if (symbol? name) name (last name)) 
                   ....  ; indicate the place where language name is (replaced with explicit requires)
                   ; The submodule baz in submodule bar in module foo is '(foo bar baz).
                   ; so (last name) gets the name of the submodule.
                   ,@(if (null? flags) '() (list `(quote ,flags))) ; if present show flags
                   ; now the list of requires 
                   ,@(let ([l (apply
                               append
                               (for/list ([req (in-list requires)]
                                          #:when (pair? (cdr req)))
                                 ; produce list of symbols and/or module paths as strings
                                 (define l (for/list ([mpi (in-list (cdr req))])
                                             (define p (mpi->string mpi))
                                             (if (path? p)
                                                 (let ([d (current-load-relative-directory)])
                                                   (path->string 
                                                    (if d
                                                        (find-relative-path (simplify-path d #t)
                                                                            (simplify-path p #f) 
                                                                            #:more-than-root? #t)
                                                        p)))
                                                 p)))
                                 (if (eq? 0 (car req))                    ; phase 0 just use as is
                                     l
                                     `((,@(case (car req)
                                            [(#f) `(for-label)]           ; phase #f means for-label
                                            [(1) `(for-syntax)]           ; phase 1        for-syntax
                                            [else `(for-meta ,(car req))]); otherwise use  for-meta
                                        ,@l)))))])
                       (if (null? l) null `((require ,@l))))
                   ; the definitions from the decompilation of the prefix:
                   ,@defns
                   ; the module declared submodules: 
                   ,@(for/list ([submod (in-list pre-submodules)])
                       (decompile-module submod orig-stack stx-ht 'module))
                   ; the syntax-bodies
                   ,@(for/list ([b (in-list syntax-bodies)])
                       (let loop ([n (sub1 (car b))])
                         (if (zero? n)
                             (cons 'begin
                                   (for/list ([form (in-list (cdr b))])
                                     (decompile-form form globs stack closed stx-ht)))
                             (list 'begin-for-syntax (loop (sub1 n))))))
                   ; the form
                   ,@(map (lambda (form)
                            (decompile-form form globs stack closed stx-ht))
                          body)
                   ; and finally the module* declared sudmodules
                   ,@(for/list ([submod (in-list post-submodules)])
                       (decompile-module submod orig-stack stx-ht 'module*))))]
    [else (error 'decompile-module "huh?: ~e" mod-form)]))

; (struct form zo ())
;   Form is the super-type for all form that can appear in compiled code
;   except for literals that are represented as themselves.

; decompile-form : form glob-desc stack closed stx-ht -> s-exp
;   globs  = (glob-desc vars num-tls num-stxs num-lifts)) produced by decompile-prefix
;   stack  = a list of symbols representing the contents of the stack
;            the top of the stack has index 0
;   closed = is an hasheq-table from ... to ...
;   stx-ht = is a hashtable from wrapped syntax objects to decompiled syntax objects
(define (decompile-form form globs stack closed stx-ht)
  (match form
    [(? mod?)
     (decompile-module form stack stx-ht 'module)]
    [(struct def-values (ids rhs)) 
     ; Each id is a toplevel: (struct toplevel expr (depth pos const? ready?))
     ; A toplevel represents a reference to a top-level or imported variable via the prefix array. 
     ; The depth field indicates the number of stack slots to skip to reach the prefix array, 
     ; and pos is the offset into the array.     
     `(define-values ,(map (lambda (tl)
                             (match tl
                               [(struct toplevel (depth pos const? set-const?))
                                ; here pos is used to find the identifier
                                ; (but depth is not used)
                                (list-ref/protect (glob-desc-vars globs) pos 'def-vals)]))
                           ids)
        ,(if (inline-variant? rhs) ; an inline-variabn can be used for cross-module inlining
             `(begin               ; if present there is both an inline and a direct variant
                ,(list 'quote '%%inline-variant%%)
                ,(decompile-expr (inline-variant-inline rhs) globs stack closed)
                ,(decompile-expr (inline-variant-direct rhs) globs stack closed))
             (decompile-expr rhs globs stack closed)))]
    [(struct def-syntaxes (ids rhs prefix max-let-depth dummy))
     ; def-syntaxes uses their own prefix, so "install" it and then do as in def-values 
     `(define-syntaxes ,ids
        ,(let-values ([(globs defns) (decompile-prefix prefix stx-ht)])
           `(let ()
              ,@defns
              ,(decompile-form rhs globs '(#%globals) closed stx-ht))))]
    [(struct seq-for-syntax (exprs prefix max-let-depth dummy))
     ; a define-syntaxes or begin-for-syntax form, decompile both to (begin-for-syntax ...)
     `(begin-for-syntax
        ,(let-values ([(globs defns) (decompile-prefix prefix stx-ht)])
           `(let ()
              ,@defns
              ,@(for/list ([rhs (in-list exprs)])
                  (decompile-form rhs globs '(#%globals) closed stx-ht)))))]
    [(struct seq (forms))
     ; represents a begin or splice form
     `(begin ,@(map (lambda (form)
                      (decompile-form form globs stack closed stx-ht))
                    forms))]
    [(struct splice (forms))
     `(begin ,@(map (lambda (form)
                      (decompile-form form globs stack closed stx-ht))
                    forms))]
    [(struct req (reqs dummy))
     ; a top-level require (but not in a module form) 
     `(#%require . (#%decode-syntax ,reqs))]
    [else
     (decompile-expr form globs stack closed)]))

(define (extract-name name)
  (if (symbol? name)
      (gensym name)
      (if (vector? name)
          (gensym (vector-ref name 0))
          #f)))

(define (extract-id expr)
  (match expr
    [(struct lam (name flags num-params arg-types rest? closure-map closure-types tl-map 
                       max-let-depth body))
     (extract-name name)]
    [(struct case-lam (name lams))
     (extract-name name)]
    [(struct closure (lam gen-id))
     (extract-id lam)]
    [else #f]))

(define (extract-ids! body ids)
  ; used to decompile let-void  which pushes an number of uninitilized slots on the stack
  ; while decompiling (struct let-void (count boxes? body)) the call
  ; (extract-ids! body ids) is made to fill in the vector ids of identifiers
  ; the ids are generated elsewhere, so they need to be extracted
  (match body
    [(struct let-rec (procs body))
     (for ([proc (in-list procs)]
           [delta (in-naturals)])
       (when (< -1 delta (vector-length ids))
         (vector-set! ids delta (extract-id proc))))
     (extract-ids! body ids)]
    [(struct install-value (val-count pos boxes? rhs body))
     (extract-ids! body ids)]
    [(struct boxenv (pos body))
     (extract-ids! body ids)]
    [else #f]))

(define (decompile-tl expr globs stack closed no-check?)
  (match expr
    [(struct toplevel (depth pos const? ready?))
     ; Represents a reference to a top-level or imported variable via the prefix array. 
     (let ([id (list-ref/protect (glob-desc-vars globs) pos 'toplevel)]) ; pos index in prefix array
       (cond
         ; references to potentially uninitialized slots mut be checked, see if a check is needed:
         [no-check? id]              
         [(and (not const?) (not ready?))
          `(#%checked ,id)]
         #;[(and const? ready?) `(#%const ,id)]
         #;[const? `(#%iconst ,id)]
         [else id]))]))

(define (decompile-expr expr globs stack closed)
  (match expr
    [(struct toplevel (depth pos const? ready?))
     (decompile-tl expr globs stack closed #f)]
    [(struct varref (tl dummy))
     `(#%variable-reference ,(if (eq? tl #t)     ; original reference was to a contant local binding
                                 '<constant-local>
                                 (decompile-tl tl globs stack closed #t)))]
    [(struct topsyntax (depth pos midpt))
     ; Represents a reference to a quoted syntax object via the prefix array.
     (list-ref/protect (glob-desc-vars globs) (+ midpt pos) 'topsyntax)]
    [(struct primval (id))
     ; Represents a direct reference to a variable imported from the run-time kernel.
     (hash-ref primitive-table id (lambda () (error "unknown primitive")))]
    [(struct assign (id rhs undef-ok?))
     ; Represents a set! expression that assigns to a top-level or module-level variable. 
     ; (Assignments to local variables are represented by install-value expressions.)
     ; After rhs is evaluated, the stack is restored to its depth from before evaluating rhs.
     `(set! ,(decompile-expr id globs stack closed)
            ,(decompile-expr rhs globs stack closed))]
    [(struct localref (unbox? offset clear? other-clears? type))
     ; Represents a local-variable reference; 
     ; it accesses the value in the stack slot after the first pos slots. 
     (let ([id (list-ref/protect stack offset 'localref)])
       (let ([e (if unbox?          ; unbox if needed
                    `(#%unbox ,id)  
                    id)])
         (if clear?                 ; clear if needed (to allow reclamation of the value as garbage)
             `(#%sfs-clear ,e)
             e)))]
    [(? lam?)
     `(lambda . ,(decompile-lam expr globs stack closed))]
    [(struct case-lam (name lams))
     ; Represents a case-lambda form as a combination of lambda forms that are tried (in order) 
     ; based on the number of arguments given.
     `(case-lambda
        ,@(map (lambda (lam)
                 (decompile-lam lam globs stack closed))
               lams))]
    [(struct let-one (rhs body type unused?))
     ; Pushes an uninitialized slot onto the stack, evaluates rhs and 
     ; puts its value into the slot, and then runs body. 
     ; type is one of #f 'flonum 'fixnum 'extflonum
     ; If type is not #f, then rhs must produce a value of the corresponding type, 
     ; and the slot must be accessed by localrefs that expect the type.
     ; Restores stack depth.
     (let ([id (or (extract-id rhs)
                   (gensym (or type (if unused? 'unused 'local))))])
       `(let ([,id ,(decompile-expr rhs globs (cons id stack) closed)])
          ,(decompile-expr body globs (cons id stack) closed)))]
    [(struct let-void (count boxes? body))
     ; Pushes count uninitialized slots onto the stack and then runs body.
     ; If boxes? is #t, then the slots are filled with boxes that contain #<undefined>.
     (let ([ids (make-vector count #f)])
       (extract-ids! body ids)
       (let ([vars (for/list ([i (in-range count)]
                              [id (in-vector ids)])
                     (or id (gensym (if boxes? 'localvb 'localv))))])
         `(let ,(map (lambda (i) `[,i ,(if boxes? `(#%box ?) '?)])
                     vars)
            ,(decompile-expr body globs (append vars stack) closed))))]
    [(struct let-rec (procs body))
     ; Represents a letrec form with lambda bindings:
     ;     (letrec ([id (lambda ...)] ...) body)
     `(begin
        (#%set!-rec-values ,(for/list ([p (in-list procs)]
                                       [i (in-naturals)])
                              (list-ref/protect stack i 'let-rec))
                           ,@(map (lambda (proc)
                                    (decompile-expr proc globs stack closed))
                                  procs))
        ,(decompile-expr body globs stack closed))]
    [(struct install-value (count pos boxes? rhs body))
     ; Runs rhs to obtain count results, and installs them into existing slots on the stack in order, 
     ; skipping the first pos stack positions. 
     `(begin
        (,(if boxes? '#%set-boxes! 'set!-values)
         ,(for/list ([i (in-range count)])
            (list-ref/protect stack (+ i pos) 'install-value))
         ,(decompile-expr rhs globs stack closed))
        ,(decompile-expr body globs stack closed))]
    [(struct boxenv (pos body))
     ; Skips pos elements of the stack, setting the slot afterward to a new box containing 
     ; the slot’s old value, and then runs body.
     (let ([id (list-ref/protect stack pos 'boxenv)])
       `(begin
          (set! ,id (#%box ,id))
          ,(decompile-expr body globs stack closed)))]
    [(struct branch (test then else))
     `(if ,(decompile-expr test globs stack closed)
          ,(decompile-expr then globs stack closed)
          ,(decompile-expr else globs stack closed))]
    [(struct application (rator rands))
     ; Represents a function call. The rator field is the expression for the function, 
     ; and rands are the argument expressions.
     ; Before any of the expressions are evaluated, (length rands) uninitialized stack slots 
     ; are created (to be used as temporary space).
     (let ([stack (append (for/list ([i (in-list rands)]) (gensym 'rand)) ; push slots
                          stack)])
       (annotate-unboxed
        rands
        (annotate-inline
         `(,(decompile-expr rator globs stack closed)
           ,@(map (lambda (rand)
                    (decompile-expr rand globs stack closed))
                  rands)))))]
    [(struct apply-values (proc args-expr))
     `(#%apply-values ,(decompile-expr proc globs stack closed) 
                      ,(decompile-expr args-expr globs stack closed))]
    [(struct seq (exprs))
     `(begin ,@(for/list ([expr (in-list exprs)])
                 (decompile-expr expr globs stack closed)))]
    [(struct beg0 (exprs))
     ; restores stack depth
     `(begin0 ,@(for/list ([expr (in-list exprs)])
                  (decompile-expr expr globs stack closed)))]
    [(struct with-cont-mark (key val body))
     `(with-continuation-mark
          ,(decompile-expr key globs stack closed)
        ,(decompile-expr val globs stack closed)
        ,(decompile-expr body globs stack closed))]
    [(struct closure (lam gen-id))
     ; A lambda form with an empty closure, which is a procedure constant.
     (if (hash-ref closed gen-id #f) ; generate an identifier and save it for later use in closed
         gen-id
         (begin
           (hash-set! closed gen-id #t)
           `(#%closed ,gen-id ,(decompile-expr lam globs stack closed))))]
    ; and finally literals
    [else `(quote ,expr)])) 

(define (decompile-lam expr globs stack closed)
  (match expr
    [(struct closure (lam gen-id)) (decompile-lam lam globs stack closed)]
    [(struct lam (name  ; for debugging purposes
                  flags ; 'preserves-marks 'is-method 'single-result
                  ;       'only-rest-arg-not-used 'sfs-clear-rest-args
                  num-params  ; number of arguments accepted by the procedure, 
                  ;           ; not counting a rest argument
                  arg-types   ; (listof (or/c 'val 'ref 'flonum 'fixnum 'extflonum))
                  ;           ; 'val = normal argument, 'ref = boxed
                  rest?       ; are rest arguments accepted? if so they are 
                  ;           ; collected into a "rest" variable
                  closure-map ; vector of stack-positions captured when lambda is evaluated
                  closure-types ; types corresponding to the captured variables
                  tl-map        ; indicates which toplevel variables actually used
                  max-let-depth ; indicates the maximum stack depth created by body plus 
                  ;             ; the arguments and closure-captured values pushed onto the stack
                  body))        ; expr
     (let ([vars (for/list ([i    (in-range num-params)]
                            [type (in-list  arg-types)])
                   (gensym (format "~a~a-" 
                                   (case type 
                                     [(ref) "argbox"] 
                                     [(val) "arg"]
                                     [else (format "arg~a" type)])
                                   i)))]
           [rest-vars (if rest? (list (gensym 'rest)) null)]
           [captures (map (lambda (v)
                            (list-ref/protect stack v 'lam))
                          (vector->list closure-map))])
       ; the lambda / case-lambda are consed elsewhere, so begin with the argument list:
       `((,@vars . ,(if rest?
                        (car rest-vars)
                        null))
         ; the name for debugging purposes
         ,@(if (and name (not (null? name)))
               `(',name)
               null)
         ; flags
         ,@(if (null? flags) null `('(flags: ,@flags)))
         ; list the captures
         ,@(if (null? captures)
               null
               `('(captures: ,@(map (lambda (c t)
                                      (if t
                                          `(,t ,c)
                                          c))
                                    captures
                                    closure-types)
                             ,@(if (not tl-map)
                                   '()
                                   (list
                                    (for/list ([pos (in-set tl-map)])
                                      (list-ref/protect (glob-desc-vars globs)
                                                        (if (or (pos . < . (glob-desc-num-tls globs))
                                                                (zero? (glob-desc-num-stxs globs)))
                                                            pos
                                                            (+ pos (glob-desc-num-stxs globs) 1))
                                                        'lam)))))))
         ,(decompile-expr body globs
                          (append captures
                                  (append vars rest-vars))
                          closed)))]))

(define (annotate-inline a)
  a)

(define (annotate-unboxed args a)
  a)

;; ----------------------------------------

#;
(begin
  (require scheme/pretty)
  (define (try e)
    (pretty-print
     (decompile
      (zo-parse (let-values ([(in out) (make-pipe)])
                  (write (parameterize ([current-namespace (make-base-namespace)])
                           (compile e))
                         out)
                  (close-output-port out)
                  in)))))
  (pretty-print
   (decompile
    (zo-parse 
     (open-input-file 
      "/home/mflatt/proj/plt/collects/tests/mzscheme/benchmarks/common/sboyer_ss.zo"))))
  #;
  (try '(lambda (q . more)
          (letrec ([f (lambda (x) f)])
            (lambda (g) f)))))