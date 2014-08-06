#lang racket/base
(require unstable/syntax) ; for phase-of-enclosing-module

;;; Jens Axel Søgaard, July 2014
;;; Goal: Understand how bytecodes work in Racket.
;;;       Make an interpreter for bytecodes in Racket.

;;; Features
; * All bytecodes are implemented
; * Explicit simulation of the stack and the use of prefix arrays
; * Multiple values are supported
; * Explicit allocation of closures from lambda, case-lambda and let-rec respectively.
; * Closures can be applied by Racket procedures such as map and apply
; * Top-level variables are represented as a standard namespace
; * Modules represented as standard modules
; * Import from standard Racket modules are supported
; * Exports are supported (rename-out is not supported though)

;;; Missing
; * Submodules ignored for now

; * Primitives that manipulate the (Racket) stack need to be overridden
;   so they know about the simulated stack. 
;   (That is call/cc, dynamic-wind are out of order)

; * Use eval-zo directly in the DrRacket repl [easy fix]
;   [ (current-eval eval-zo) fails: real eval calls (current-eval ]

;;; Ideas for further exploration
; * Increase detail of simulation:
;     - Multiple values
;     - Implement namespace and module registry
;     - continuation marks
;     - dynamic-wind, prompts and continuations

(provide (all-defined-out))

;;;
;;; Imports
;;; 
(require compiler/zo-structs      ; structures definitions for zo-structs (represents bytecode)
         compiler/zo-parse        ; parses bytecode to zo structures that represents bytecode
         compiler/zo-marshal      ; converts zo to bytecode
         racket/fasl              ; (unused) converts bytecode in byte string for to s-exp
         compiler/decompile       ; converts zo to human readable s-exp
         racket/undefined         ; (could be) used to fill uninitialized slots
         syntax/modcollapse       ; used to simplify module paths
         ; syntax/modread         ; (unused) read modules 
         syntax/modresolve        ; resolving module paths to file paths
         ; standard racket libraries
         racket/port racket/match racket/list racket/path racket/format
         ; a couple of test macros use syntax/parse
         (for-syntax syntax/parse racket/base))
;;;
;;; OVERVIEW
;;;

; The procedures  read  and  compile  are enough to produce raw bytecode.
;     (compile (read (open-input-string "(+ 1 2)")))  
; The result of compile is a compiled-expression and is basically a byte string.
; We want to work with structures representing the bytecode. 
; The module compiler/zo-structs contain structure definitions used to 
; represent the bytecode as structs. The structures are named zo structs or
; just zo for short. 
; The module compiler/zo-parse contains a parser that produce zo structures.

; Standard evaluation of a piece of text read from a port undergoes this process.

; Operation:         read       expand       compile           eval   
; Type:        port   ->   s-exp  ->  syntax    ->    bytecode  ->  value

; [Aside: Internally eval generates machine code from the bytecode, 
;         which is executed to produce the values.]

; It doesn't take long to realize that 

;   (eval (compile (expand (read (open-input-string "(+ 1 2)")))))

; is bothersome to type over and over again while testing an interpreter. 
; Consequently eval will automatically invoke the invoke the expander and compiler.

; Note:      (eval                  s-exp) 
;          = (eval (compile         s-exp))
;          = (eval (compile (expand s-exp)))

; The example now becomes:   (eval '(+ 1 2))

; The function compile produce bytecode.
; The actual bytecode looks something like this:  #~6.0.1.13T ...gibberish...
; The #~ indicates it is bytecode. The 6.0.1.13 is the version of Racket
; used to produce the bytecode and then random characters are displayed.

; In order to examine the bytecode we need to parse into a more human readable format.
; The module compiler/zo-parse contains a parser that parses byte strings containing
; bytecode in to zo-structures. The name zo doesn't mean anything. It is an
; old pun and stands for Zodiac. Here zo structures simply represents bytecode
; as structures.

; The evaluator eval-zo implemented here use zo as input. A parser
; from bytecode to zo is needed. The parser zo-parse from compiler/zo-parse
; parses from byte strings to zo. A little step to convert from
; bytecode to byte string is needed.

; Operation:       expand     compile      convert    zo-parse   eval-zo
; Type:        s-exp ->  syntax  ->   bytecode -> bytes  ->    zo  -> value

; convert : bytecode -> bytes
(define (convert bytecode) 
  (open-input-bytes (with-output-to-bytes (λ () (write bytecode)))))

; Since expander, compiler and evaluator work together, we will define 
; our own set: 
;    expand-zo  : expands s-exp to syntax object
;    compile-zo : compiles syntax-object to zo
;                 (if given an s-exp it invokes expand-zo)
;                 (if given bytecode it invokes convert)
;    eval-zo    : evaluates zo
;                 (if given an something else, compile-zo is invoked)

; [We will soon get to actual code, but we need an aside first.]

;;;
;;; NAMESPACES
;;;

; The function read needs no context to parse a string "(+ 1 2)" into '(+ 1 2).
; The functions expand, compile and eval all need to happen in a context.
; To evaluate '(+ 1 2) there needs to association between the '+ and the 
; primitive addition operation. 

; Standard Racket use  namespaces  to represent such associations
; and we will use these as-is.
; A namespace must not be confused with an environment.
; A namespace is a *top-level* mapping from symbols to identifiers.
; That is: local variables are not stored in the namespace.

; Expand uses the namespace given by the parameter current-namespace.
; Let's see the effect it has on expansion:
;   > (parameterize ([current-namespace (make-empty-namespace)]) (expand '(+ 1 2)))
;   +: unbound identifier;
; In an empty namespace + has no binding, so we get an error.
; In a #lang racket repl, we get:
;   > (expand '(+ 1 2))
;   <syntax-object: (#%app + (quote 1) (quote 2))>

; Since we will be do a *lot* of testing in the DrRacket repl, it is
; not ideal to use the more-or-less random namespace in current-namespace.
; At least not in the beginning. Our standard namespace for testing
; will be produced by make-start-namespace and used automatically
; by expand-zo, compile-zo and eval-zo. If we use DrRacket's
; current-namespace we will compile will error-tracing enabled,
; which will make our first programs more complicated than need be.

; Well, later it becomes important for evaluation to use the
; same namespace as compile - at that point the current-namespace
; convention is the right thing. 

(define use-start-or-current 'start)
(define (use-start)   (set! use-start-or-current 'start))
(define (use-current) (set! use-start-or-current 'current))

; make-start-namespace : -> namespace
;   like make-base-empty-namespace but also attaches 'racket/list
(define (make-start-namespace)
  (case use-start-or-current
    [(start)    (define ns (make-base-empty-namespace))
                (parameterize ([current-namespace ns])
                  ; The start-namespace imports #%kernel 
                  ; contains most of the primitives in Racket. 
                  (namespace-require ''#%kernel)
                  (namespace-require 'racket/base)
                  ; racket/list is imported to make tests more interesting
                  ; The racket/list module provides procedures implemented in Racket
                  ; (we need to test that application works with both primitives and procedures)
                  (namespace-require/copy 'racket/list))
                ns]
    [(current) (current-namespace)]
    [else      (error 'make-start-namespace "expected 'start or 'current in use-start-or-current")]))

; A little syntax makes life sweeter.

; syntax: (with-start-namespace body ...)
;   Parameterize current-namespace with the result of (make-start-namespace)
;   and evaluate the bodies. The result of the last body is returned.
(define-syntax (with-start-namespace stx)
  (syntax-parse stx
    [(_ body ...+)
     #'(parameterize ([current-namespace (make-start-namespace)])
         body ...)]))

; syntax: (start-begin form ...)
;    Evaluate each form ... in order were the parameter current-namespace 
;    is set to the result of (make-start-namespace).
(define-syntax (start-begin stx)
  (syntax-parse stx
    [(_ form ...)
     #'(begin (with-start-namespace form ...))]))

;;;
;;; EXPANSION
;;;

(define (expand-zo s-exp [ns (make-start-namespace)])
  (parameterize ([current-namespace ns])
    (expand s-exp)))

;;;
;;; COMPILATION 
;;;

; Here are the basic operations we will use:

; Operation:     s-exp->bytecode        bytecode->zo     
; Type:      sexp     ->          bytecode   ->    zo       

(define bytecode? compiled-expression?)

; compile-zo : (or/c s-exp bytecode?) [namespace] -> zo
(define (compile-zo s-exp [ns (make-start-namespace)])
  (parameterize ([current-namespace ns]
                 ; we allow set! to undefined variables, due to the way we 
                 ; implement modules [see eval-module]
                 [compile-allow-set!-undefined #f])
    (match s-exp 
      [(? bytecode? bc) (bytecode->zo bc)]
      [_                (define bc (s-exp->bytecode s-exp ns))
                        (bytecode->zo bc)])))

(define (s-exp->bytecode s-exp [ns (make-start-namespace)])
  (parameterize ([current-namespace ns]
                 [compile-allow-set!-undefined #f])
    (compile s-exp)))

(define (bytecode->zo bytecode)
  (zo-parse (convert bytecode)))

;;; Example

; We are finally in a position to sudy some real bytecode.

; > (compile-zo '(+ 1 2))
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
;   > (compile-zo '((lambda (x) (+ 1 x)) 2))
;   '#s((compilation-top zo 0) 0 #s((prefix zo 0) 0 () ()) 3)

; And for completeness sake:

(define (string->bytecode str [ns (make-start-namespace)])
  (s-exp->bytecode (read (open-input-string str)) ns))

(define (string->zo str [ns (make-start-namespace)])
  (bytecode->zo (string->bytecode str ns)))

;;;
;;; SANITY CHECK / CHEATING
;;;

; It is convenient to compare the output of eval-zo with
; the result of the standard racket evaluator.
; It will also allow us to convert zo-syntax-objects into real syntax objects.

(define (racket-eval-zo zo [ns (make-start-namespace)])
  ; note: zo-marshal does not support top-level require
  (parameterize ([current-namespace ns] [read-accept-compiled #t])
    (eval 
     (read
      (open-input-bytes 
       (zo-marshal zo)))))) 

; this one works too 
;  [tell me where the docs say that eval know how to evaluate compiled expressions]
#;(define (racket-eval-zo zo [ns (make-start-namespace)])
    (parameterize ([current-namespace ns])
      (fasl->s-exp 
       (open-input-bytes 
        (zo-marshal zo)))))

; stx->syntax : stx -> syntax
;  convert a zo representing a syntax-object
;  the conversion was made by imitating the output of (s-exp->zo '#'x))
(define (stx->syntax stx)
  (racket-eval-zo (compilation-top 0 (prefix 0 '() (list stx)) (topsyntax 0 0 0))))

;;;
;;; LOCAL VARIABLES AND THE STACK REGISTER
;;;

; The Racket virtual machine use a stack to store local variables.
; Here a mutable list, an mlist, is used. An alternative would
; be to use lists of boxes.

(define stack '())  ; a global variable holds the stack.

;;;
;;; MUTABLE LISTS (mlists)
;;;

; A few operations on mutable lists are needed.
; [ racket/mlist needs some love ]

(require compatibility/mlist) 
(define (make-mlist n [val #f]) 
  (let loop ([xs '()] [n n]) 
    (if (zero? n) xs (loop (mcons val xs) (- n 1)))))
(define (mdrop xs n) ; drop n mpairs
  (let loop ([xs xs] [n n]) 
    (if (zero? n) xs (loop (mcdr xs) (- n 1)))))
(define (msplit-at list0 n0)
  (let loop ([list list0] [n n0] [pfx '()])
    (cond [(zero? n) (values (mreverse pfx) list)]
          [(mpair? list) (loop (mcdr list) (sub1 n) (mcons (mcar list) pfx))]
          [else (error 'msplit-at "count too large, got: ~a ~a" list0 n0)])))
(define (append-vector-to-mlist v xs)
  (define n (vector-length v))
  (for/fold ([xs xs]) ([i (in-range (- n 1) -1 -1)])
    (mcons (vector-ref v i) xs)))
;;; 
;;; Primitives
;;;

; Procedures implemented in the C runtime are called primitives.
; [As of July 2014 there are 1096 primitives!]
; In bytecode they are referred to by index (number). 

; There is no builtin way to access primitives by number,
; so we construct a little bytecode program, that evaluates
; to the corresponding primitive.

; get-primitive : index -> primitive
(define (get-primitive index)
  ; todo: cache these in a vector
  (racket-eval-zo (compilation-top 0 (prefix 0 '() '()) (primval index))))


; When reading bytecode it is convenient to see a name instead,
; so we need a table that maps the index to the name of the primitive.

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

(define primitive-table  ; hashtable from index to primitive
  (let ([ns (make-base-empty-namespace)])           ; make namespace with racket/base attached
    (parameterize ([current-namespace ns])
      (namespace-require ''#%kernel)                ; import all primitives
      (namespace-require ''#%unsafe)
      (namespace-require ''#%flfxnum)
      (namespace-require ''#%extfl)
      (namespace-require ''#%futures)
      (namespace-require ''#%foreign)
      ; For each symbol we need to find its index. We do this by compiling a 
      ; reference to it and picking the index out of the resulting bytecode.
      ; Example: The index of namespace-variable-values is 1077.
      ;  (compile-zo 'namespace-variable-value) 
      ;   '#s((compilation-top zo 0) 0 #s((prefix zo 0) 0 () ()) 
      ;      #s((primval expr 0 form 0 zo 0) 1077))
      ; The index of namespace-variable-value is 1077.
      (define (symbol->index sym)
        (with-handlers ([exn:fail? (lambda (x) #f)])
          (match (compile-zo sym)
            [(struct compilation-top (_ prefix (struct primval (n)))) n]
            [else #f])))
      ; we will store out results in a hash-table
      (define table (make-hash))
      (for/list ([sym (namespace-mapped-symbols)])
        (define index (symbol->index sym))
        (when index (hash-set! table sym index)))
      table)))

;;;
;;; Decompilation
;;;

; The module compiler/decompile provides a decompiler from bytecode
; to readable s-expressions. That can handy at times.
; See the documentation for the identifier conventions used.

; > (use-start) (decompile (compile-zo '(+ x 1)))
; '(begin (+ (#%checked _x) '1))


;;;
;;; XXX
;;;



; Top-level and module-level variable are managed in a namespace.
; A name associates a symbols with buckets (think boxes) which
; contain the value of the variable. Importing a module
; does note create new buckets. Importing simply redirects
; access to the (shared) buckets.




(define (get-imported id pos modidx)
  ; note: (dynamic-require mod id) won't works since id can be a non-exported identifier
  (define mod (module-path-index-resolve modidx))
  ; (define exports (call-with-values (λ() (module->exports mod)) vector))
  ; note: (vector-ref exports pos) will give the entry of id
  ; The current-namespace has a module registry.
  (dynamic-require mod #f)  ; Register and instantiate the module mod if not already
  ; Look up id in the namespace belonging to mod 
  (namespace-variable-value id #f (λ () (error)) (module->namespace mod)))

; get-imported : 
;   get the value of an imported module-variable
;   this is only called by eval-prefix
;   Racket's builtin eval and compile is used to get the value.
;   Note: This low-level version works as well.

#;(define (get-imported id pos modidx)
    (displayln (list 'get-imported id pos (mpi->string modidx)))
    (racket-eval-zo 
     (compilation-top 0 ; max-let-depth
                      (prefix 0 (list (module-variable modidx id pos 0 #f)) '())
                      (toplevel 0 0 #t #t))))


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


;;;
;;; EXTRA BYTE CODES
;;; 

; We will add two byte codes not present in the real Racket VM here.
; The first, trace, is for debugging. The second is used to implement modules.

(define-struct (trace form) (form) #:transparent)
; Display the stack, then evaluate form.

(define-struct (module-body form) (prefix forms) #:transparent)
; Push the prefix to the stack, then evaluate the forms.


;;;
;;; EVALUATION
;;;

; And finally... here comes the beginning of the evaluator.

; The result of compile-zo is a compilation-top, so that's where the
; decompilation process begins.

; (struct compilation-top zo (max-let-depth prefix form)

; The compilation-top consists of code (form), which are instructions to run on a stack machine.
; The max-let-depth is maximum stack depth that code creates (not counting the prefix array).
; The prefix describes what the runtime must push on the stack before executing code.

; Since we have as many mpairs to our disposal as we want, we will ignore max-let-depth.
; A nice exercise would be to replace the stack representation from mlists to a vector
; base one.

; eval-zo : compilation-top [namespace] -> values(s)
(define (eval-zo zo [ns (make-start-namespace)])
  ; If zo is a zo structure (representing bytecode) evaluate it.
  ; If zo is an s-expression, then compile it before evaluating it.
  (cond [(zo? zo) (unless (compilation-top? zo)
                    (error 'eval-zo "expected a compilation-top, got ~a" zo))
                  ; evaluation always occur within a top-level namespace
                  ; if none are given (make-start-namespace) is used
                  (parameterize ([current-namespace ns])
                    (eval-top zo))]
        [else      (eval-zo (compile-zo zo ns) ns)]))

; eval-top : compilation-top -> value(s)
(define (eval-top top)
  (match top
    [(struct compilation-top (max-let-depth prefix form))
     ; the prefix describes an array of variables that must be pushed to the stack ...
     (define array (eval-prefix prefix))
     (set! stack (mlist array))
     ; ... before form is evaluated
     (eval-form form)]
    [else (error 'eval-top "unrecognized: ~e" top)]))

;;;
;;; PREFIX ARRAYS
;;;

; The evaluation in eval-top begins by pushing a prefix array onto the stack.
; Here a simple vector is used to store the array.
; But what does the prefix description look like in the bytecode?

; (struct prefix zo (num-lifts toplevels stxs)
; At runtime a prefix is an array holding variables. 
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
 
; We will use a mutable list to represent the stack. Local variables will be stored directly 
; into the mcars. 

; Top level (and imported module) variables (i.e. namespace variables) are stored 
; in the namespace.
; More precisely they are stored in buckets. When the prefix is initialized
; the bucket of a global variable are put into the prefix.
; That is: import does not create new top-level variables !
; Importing variables from a module will redirect access to the (shared) buckets.

; In the interpreter we use a standard racket namespace to represent top-level variables,
; but we use our own prefix representation. This implies that using the standard Racket
; require to import modules, will store the imported variables
; in the prefix of the Racket vm - and but not in our prefix.

; We can't get to the buckets (??? or can we via the FFI ???) so we store 
; an instance of (struct global (sym)) in our prefix array. At variable lookup time 
; a lookup of a global, will use namespace-variable-value to get the value from the namespace.
; See array-ref and array-set and the req section of eval-for for more information.

(struct global (sym ns) #:transparent)
(define (create-global sym) (global sym (current-namespace)))

; get-array : natrual -> vector
;  get the prefix array stored in stack at the given depth
(define (get-array depth)
  (mcar (mdrop stack depth)))

; array-ref : depth pos -> value
;   Get the value with position pos (index into the array)
;   in the prefix stored at the stack in the given depth.
;   A reference to a top-level variable will be redirected
;   to the actual bucket.
(define (array-ref depth pos)
  ; (displayln (list 'array-ref 'phase: (current-phase) depth pos (get-array depth)))
  (define val (vector-ref (get-array depth) pos))
  (match val
    [(global sym ns)
     ; Global variables are stored directly in the namespace.
     ; in order to work with require, which imports into the real racket prefix
     (define p (current-phase))
     (if (= p 0)
         (namespace-variable-value sym #t (λ () 'undefined-global) ns) ; fast path
         (namespace-variable-value-in-phase sym p ns))]
    [else val]))

; array-set! : natural natural value -> void
;  set the variable at the given depth and position
;  assignments to top-level variables are redirected
(define (array-set! depth pos val)
  ; In principle a simple vector-set!, but we need to redirect assignments
  ; to global variables, which are stored in Racket's buckets.
  ; The only complication is that there are different buckets for each phase
  ; and namespace-set-variable-value! only supports phase 0.
  (define array (get-array depth))
  (define old-val (vector-ref array pos))  
  (match old-val
    [(global sym ns) (define p (current-phase))
                     (if (= p 0) 
                         (namespace-set-variable-value! sym val #t ns) ; fast path 
                         (namespace-set-variable-value-in-phase! sym val p ns))]
    [else            (vector-set! array pos val)]))

; namespace-variable-value-in-phase : symbol nonnegative-integer -> value
;   in phase p get value of x
(define (namespace-variable-value-in-phase x p ns)
  ; (displayln (list 'namespace-variable-value-in-phase x p ns))
  (unless (and (integer? p) (not (negative? p))) (error))
  (define (on-fail) '<undef-global>)
  (parameterize ([current-namespace ns])
    (eval (wrap-expr-for-meta p `(namespace-variable-value ',x #t ,on-fail)))))

; namespace-set-variable-value-in-phase! : sym value nonnegative-integer -> void
;   in phase p set value of x to v
(define (namespace-set-variable-value-in-phase! x v p ns)
  ; (displayln (list 'namespace-set-variable-value-in-phase! x v p ns))
  (unless (and (integer? p) (not (negative? p))) (error))
  (define (build p e) (if (= p 0) e (build (- p 1) `(begin-for-syntax ,e))))
  (parameterize ([current-namespace ns])
    (eval (wrap-begin-for-meta p `(namespace-set-variable-value! ',x ,v #t)))))

; wrap-for-meta : (phase expr -> expr) phase expr
;   wrap the expression e p times using wrapper
(define (wrap-for-meta wrapper p e)
  (for/fold ([e e]) ([_ (in-range p)])
    (wrapper e)))

; wrap-begin-for-syntax : s-exp -> s-exp
(define (wrap-begin-for-syntax e) 
  `(begin-for-syntax ,e))

(define (wrap-begin-for-meta p e)
  ; no begin-for-meta in racket (?!)
  (wrap-for-meta wrap-begin-for-syntax p e))

(define (wrap-expr-for-syntax x)
  ; assume x evaluates to a single value
  `(let-syntax ([ref (λ(_) #`#,,x)]) (ref)))

(define (wrap-expr-for-meta p x)
  (wrap-for-meta wrap-expr-for-syntax p x))

;;;
;;; PREFIX EVALUATION
;;;

; eval-prefix : prefix -> vector
(define (eval-prefix a-prefix)
  (match a-prefix
    [(struct prefix (num-lifts toplevels stxs))
     ; allocate array
     (define size (+ (length toplevels) (length stxs) (if (null? stxs) 0 1) num-lifts))
     (define array (make-vector size #f)) ; could use undefined here (but #f prints smaller)
     ; fill in values for toplevel and imported variables
     (for ([i (in-naturals)] [tl (in-list toplevels)])
       (vector-set! 
        array i
        (match tl
          ; #f represents a dummy variable used to access the enclosing module 
          ; [Comment in docs for seq-for-syntaxes hits that this should be (current-namespace)?]
          [#f '#%linkage] ; todo: should that be  array  instead ? 
          ; top-level variables (outside of modules) are accessed through the current namespace
          [(struct global-bucket (name))
           ; (displayln (list 'eval-prefix 'global-bucket name))
           (create-global name)]
          [(? symbol? s) ; a symbol is a reference to a variable defined in an enclosing module
           ; (displayln (list 'prefix 'symbol: s))
           (create-global s)]
          ; variable imported from module
          [(struct module-variable (modidx sym pos phase constantness)) 
           ; (displayln (list 'module-variable modidx sym pos phase constantness))
           ; (displayln (mpi->string modidx))
           (if (and (module-path-index? modidx)
                    (let-values ([(n b) (module-path-index-split modidx)])
                      (and (not n) (not b)))) ; n = b = #f represents "self module"
               ; exercise: find a program that gets here ...
               (error 'todo: 'maybe: (vector-ref array pos))  ; identifier from this module
               (get-imported sym pos modidx))]                ; imported identifier
          [else (error 'decompile-prefix "bad toplevel: ~e" tl)])))
     ; fill in syntax-objects from stxs
     (for ([i (in-naturals (length toplevels))] [stx (in-list stxs)])
       (vector-set! array i (stx->syntax stx)))
     array]))

; mpi : module-path-index->string
;   unused (a leftover from the decompiler)
(define (mpi->string modidx)
  (cond [(symbol? modidx) modidx]
        [else (collapse-module-path-index 
               modidx (build-path (or (current-load-relative-directory) (current-directory))
                                  "here.rkt"))]))

;;;
;;; EVALUATION OF FORMS
;;;

; (struct form zo ())
;   Form is the super-type for all form that can appear in compiled code
;   except for literals that are represented as themselves.

(define (eval-forms forms)
  (match forms
    [(list)            (void)]
    [(list form)       (eval-form form)]
    [(list form forms) (eval-form form)
                       (eval-forms forms)]
    [_                 (eval-expr forms)]))

(define current-phase (make-parameter 0))

(define (eval-form form)
  (when trace-on (displayln form))
  (match form
    [(? expr? e) (eval-expr e)]
    [(struct seq (forms))
     ; evaluate forms in sequence, the last form is in tail position
     (let loop ([forms forms])
       (cond [(null? forms)        (error 'seq "empty seq")]
             [(null? (rest forms)) (eval-form (car forms))]
             [else                 (eval-form (car forms))
                                   (loop (rest forms))]))]
    [(struct splice (forms))
     ; Represents a top-level begin form where each evaluation is wrapped with a continuation prompt.
     (let loop ([forms forms])
       (cond [(null? forms)        (error 'seq "empty seq")]
             [(null? (rest forms)) (call-with-continuation-prompt	(λ() (eval-form (car forms))))]
             [else                 (call-with-continuation-prompt	(λ() (eval-form (car forms))))
                                   (loop (rest forms))]))]  
    [(struct def-values (ids rhs)) 
     ; Each id is a toplevel: (struct toplevel expr (depth pos const? ready?))
     ; A toplevel represents a reference to a top-level or imported variable via the prefix array. 
     ; The depth field indicates the number of stack slots to skip to reach the prefix array, 
     ; and pos is the offset into the array.
     (define old-stack stack)
     (define vals (call-with-values (λ () (eval-form rhs)) vector))
     (set! stack old-stack)
     (for ([id (in-list ids)] [v (in-vector vals)])
       (match-define (toplevel depth pos const? ready?) id)
       (array-set! depth pos v))]
    [(struct seq-for-syntax (forms prefix max-let-depth dummy))
     ; From the docs on begin-for-syntax:
     ;   Evaluation of an expr within begin-for-syntax is parameterized to 
     ;   set current-namespace as in let-syntax.
     ; From the docs on (let-syntax ([id trans-expr] ...) body ...+)
     ;   The evaluation of each trans-expr is parameterized to set current-namespace to a 
     ;   namespace that shares bindings and variables with the namespace being used to 
     ;   expand the let-syntax form, except that its base phase is one greater.
     (define old-stack stack)
     ; push prefix
     (define array (eval-prefix prefix))
     (set! stack (mcons array stack))
     ; evaluate forms in sequence, the last form is in tail position (?)
     (define p (current-phase))
     (parameterize ([current-phase (+ p 1)])
       ; let-syntaxes shifts the phase, 
       ; and (eval `(,eval- ...)) returns control to the meta evaluator.
       (let-syntaxes () (eval `(,eval-forms ',forms)) (values)))
     (set! stack old-stack)]
    [(struct def-syntaxes (ids rhs prefix max-let-depth dummy))
     (define old-stack stack)
     ; push prefix
     (define array (eval-prefix prefix))
     (set! stack (mcons array stack))
     ; in phase p+1 evaluate forms in sequence  (the last form is in tail position (?))
     (define p+1 (+ (current-phase) 1))
     (define returned-values #f)
     (define (return vec) (set! returned-values vec))
     (parameterize ([current-phase p+1])
       ; (define vals (call-with-values (λ () (eval-form rhs)) vector))
       (let-syntaxes                                ; shift phasae
        () (eval `(,return                          ; store in returned-values 
                   (call-with-values 
                    (λ () `(,,eval-forms ',,rhs))   ; the result of evaluting rhs
                    vector)))
        (values)))
     ; restore stack
     (set! stack old-stack)
     ; install values in the namespace
     (define ns (current-namespace))
     (for ([sym (in-list ids)] [val (in-vector returned-values)])
       (namespace-set-variable-value-in-phase! sym val p+1 ns))]
    [(struct req (reqs dummy))
     ; (displayln (list 'req (stx->syntax reqs)))
     ; This is the top-level #%require form.
     ; The syntax object reqs represents a (#%require raw-require-spec ...) form.
     ; It is the primitive import form to which require expands.
     (define #%require-form (stx->syntax reqs))
     ; Register module in namespace, instantiate it and import variables into 
     ; the prefix the racket runtime uses.
     (eval (syntax->datum #%require-form)) ; XXX TODO okay to strip ?
     ; Using (eval '(require mod)) imports mod into the current namespace.
     ; Since we are using the namespace to store top-level variables
     ; we get access to module imported variables.
     ]
    [(? mod? mod-form) ; declares a module, delegate to eval-module
     (eval-module mod-form)]
    [(module-body prefix forms) ; not in the real Racket VM
     (define old-stack stack)
     ; push prefix
     (define array (eval-prefix prefix))
     (set! stack (mcons array stack))
     ; evaluate forms
     (for ([form (in-list forms)])
       (eval-form form))
     ; pop prefix
     (set! stack old-stack)]
    ; trace is useful for debugging
    [(trace form) (displayln (list 'trace stack)) (eval-form form)]
    [else ; literals are expressions too
     (eval-expr form)]))

;;;
;;; EVALUATION OF EXPRESSIONS
;;;

; The main evaluator of expressions are eval-expr.
; The pattern:  save stack, evaluate expression, restore stack
; occurs so often that it is convenient to have eval-expr/restore
; and eval-ecpr/restore-mv. The last can handle multiple values.

(define (eval-expr/restore expr)
  (define old-stack stack)
  (define val (eval-expr expr))
  (set! stack old-stack)
  val)

(define (eval-expr/restore-mv expr)
  (define old-stack stack)
  (define vals (call-with-values (λ () (eval-form expr)) vector))
  (set! stack old-stack)
  vals)

(define trace-on #f) (set! trace-on #f)
(define (eval-expr expr)
  (when trace-on (displayln expr) (newline))
  (match expr
    [(struct toplevel (depth pos const? ready?))
     ; Represents a reference to a top-level or imported variable via the prefix array. 
     ; The depth field indicates the number of stack slots to skip to reach the prefix array, 
     ; and pos is the offset into the array.
     (array-ref depth pos)]
    [(struct topsyntax (depth pos midpt)) 
     ; Represents a reference to a quoted syntax object via the prefix array.
     (array-ref depth (+ midpt pos))]
    [(struct primval (id)) 
     ; Represents a direct reference to a variable imported from the run-time kernel.
     (get-primitive id)]
    [(struct assign (id rhs undef-ok?))
     ; Represents a set! expression that assigns to a top-level or module-level variable
     ; through an array installed by a prefix.
     ; (Assignments to local variables are represented by install-value expressions.)
     ; After rhs is evaluated, the stack is restored to its depth from before evaluating rhs.
     (match-define (toplevel depth pos const? ready?) id)
     (unless undef-ok? ; see compile-allow-set!-undefined in s-exp->zo 
       (define old-val (array-ref depth pos))
       (when (eq? old-val undefined)
         ; TODO: figure out how to find the name of the offending variable
         (error 'set! "assignment disallowed;\n cannot set undefined\n variable: XXX")))
     (define val (eval-expr/restore rhs))
     (array-set! depth pos val)]
    [(struct localref (unbox? offset clear? other-clears? type))
     (define v (mlist-ref stack offset))  ; todo: handle clear? (to ensure safe-for-space)
     (define val (if unbox? (unbox v) v))
     (when (eq? val 'undef)
       (newline)
       (displayln (list 'local-ref "reference to undef" offset stack))
       (newline) (newline))
     val]
    [(? lam? lam)  (eval-lam lam)] ; lambda expression
    [(struct case-lam (name lams))
     ; Represents a case-lambda form as a combination of lambda forms that are tried (in order) 
     ; based on the number of arguments given.     
     ; Strategy: compile case-lam into a case-clos
     ;           case-clos has a vector of arities and a a vector of clos
     ;           the arity-vector is used at application time to decide with clos to use
     ;           arities with rest arguments are represented as negative values
     ;           arity = -1  means 0 or more, arity = -2 means 1 or more, etc
     (define clos-vector (for/vector ([lam (in-list lams)]) 
                           (eval-lam lam)))
     (define arities (for/vector ([lam (in-list lams)])
                       (define n  (lam-num-params lam))
                       (define r? (lam-rest? lam))
                       (if r? (- (+ n 1)) n)))
     (case-clos name arities clos-vector)]
    [(struct let-one (rhs body type unused?)) 
     ; Pushes an uninitialized slot onto the stack, evaluates rhs and 
     ; puts its value into the slot, and then runs body. 
     ; After rhs is evaluated, the stack is restored to its depth from before evaluating rhs.
     (set! stack (mcons #f stack))
     (define val (eval-expr/restore rhs))
     ; no stack restore! 
     (set-mcar! stack val)
     (eval-expr body)]
    [(struct let-void (count boxes? body)) 
     ; Pushes count uninitialized slots onto the stack and then runs body.
     ; If boxes? is #t, then the slots are filled with boxes that contain #<undefined>.
     (let loop ([new-stack stack] [n count])
       (cond [(zero? n) (set! stack new-stack)
                        (eval-expr body)]
             [boxes?    (loop (mcons (box 'undef) new-stack) (- n 1))]
             [else      (loop (mcons      'undef  new-stack) (- n 1))]))]
    [(struct let-rec (lams body))
     ; Represents a letrec form with lambda bindings:
     ;     (letrec ([id (lambda ...)] ...) body)
     ; It allocates a closure shell for each lambda form in procs, 
     ; installs each onto the stack in previously allocated slots in reverse order 
     ; (so that the closure shell for the last element of procs is installed at stack position 0), 
     ; fills out each shell’s closure (where each closure normally references some other 
     ; just-created closures, which is possible because the shells have been installed on the stack),
     ; and then evaluates body.
     
     ; Note: The closure shells can not be omitted. If the first lambda captures the second
     ;       it will capture the value on the stack - which is undef!
     ;       Therefore: Install shells first - then the shell is captured.
     ;                  Second fill in the shells.
     ; install shells
     (let loop ([lams lams] [s stack])
       (cond [(null? lams)  (void)]
             [else          (set-mcar! s (shell #f))
                            (loop (cdr lams) (mcdr s))]))
     ; fill in lambdas
     (let loop ([lams lams] [s stack])
       (cond [(null? lams)  (void)]
             [else          (define shell (mcar s))
                            (define clos (eval-lam (first lams))) ; alloc-lam (no stack save here)
                            (set-shell-closure! shell clos)
                            (loop (cdr lams) (mcdr s))]))
     ; evaluate body
     (eval-expr body)]
    [(struct install-value (count pos boxes? rhs body))
     ; evaluate the rhs and push the result value(s)
     ; into previously allocated slots on the stack
     ; (displayln (list 'install-value count stack))
     (cond [(= count 1) ; rhs returns 1 value           
            (define val (eval-expr/restore rhs))
            (define slot (mdrop stack pos))
            (if boxes?
                (set-box! (mcar slot) val)
                (set-mcar! slot val))]
           [else        ; rhs returns multiple values
            (define vals (eval-expr/restore-mv rhs))
            (let loop ([slot (mdrop stack pos)] [count count] [i 0])
              (cond [(= count 0) (void)]
                    [else        (define val (vector-ref vals i))
                                 (if boxes?
                                     (set-box! (mcar slot) val)
                                     (set-mcar! slot val))
                                 (loop (mcdr slot) (- count 1) (+ i 1))]))])
     (eval-expr body)]
    [(struct boxenv (pos body)) 
     ; (displayln (list 'boxenv pos stack))
     (define s (mdrop stack pos))
     (set-mcar! s (box (mcar s)))
     (eval-expr body)]
    [(struct branch (test then else))
     (define val (eval-expr/restore test))
     (if val
         (eval-expr then)
         (eval-expr else))]
    [(struct application (rator rands))
     ; Represents a function call. The rator field is the expression for the function, 
     ; and rands are the argument expressions.
     ; Before any of the expressions are evaluated, (length rands) uninitialized stack slots 
     ; are created (to be used as temporary space).
     (define new-slots (make-mlist (length rands) '<app>))
     (define old-stack stack)
     (set! stack (mappend new-slots stack))      ; todo: make efficient
     (define op   (eval-expr/restore rator))
     (define args (for/list ([rand (in-list rands)]) 
                    (eval-expr/restore rand)))
     (let loop ([op op])
       (cond 
         [(clos? op)           (invoke-clos      rator rands op args old-stack)]
         [(case-clos? op)      (invoke-case-clos rator rands op args old-stack)]
         [(shell? op)          (loop (shell-closure op))]
         [(or (primitive? op)
              (continuation? op)
              (procedure? op))
          ; builtin types of procedures
          (begin0 
            (apply op args)
            (set! stack (mdrop stack (length args))))]         
         [else               
          (displayln (list 'application-error op args stack))
          (error 'app "can't apply ~a" op)]))]
    [(struct apply-values (proc args-expr))
     ; Represents (call-with-values (lambda () args-expr) proc).
     ; Note: due to left-to-right evaluation, proc is evaluated first
     (define old-stack stack)
     (define op (eval-expr proc))
     (define receiver (if (or (primitive? op) (procedure? op)) list mlist))
     (define args (call-with-values (λ () (eval-expr args-expr)) receiver))
     ; todo: use invoke-clos instead (for prettier code)
     (define (handle-clos op)
       (match-define (clos name num-params rest? captures body) op)
       ; When the function is called, the rest-argument list (if any) is pushed onto the stack, 
       ; then the normal arguments in reverse order, then the closure-captured values in 
       ; reverse order. Thus, when body is run, the first value on the stack is the first value 
       ; captured by the closure-map array, and so on.
       (define n (mlength args))
       (cond [(= n num-params)
              ; we didn't bang the operands into the new slots, so we do this (TODO)
              (set! stack (append-vector-to-mlist captures (mappend args stack)))
              (eval-expr body)]
             [(and (> n num-params) rest?)
              (define-values (mnormal mrest) (msplit-at args num-params))
              (define rest (mlist->list mrest)) ; rest is a list (used with standard apply)
              (set! stack (append-vector-to-mlist captures (mappend mnormal (mcons rest stack))))
              (eval-expr body)]
             [(> n num-params)
              (error 'app "too many argument applying ~a to ~a" op args)]
             [(< n num-params) 
              (error 'app "too few argument in application\n closure: ~a\n\n arguments: ~a"
                     op args)]))
     (let loop ([op op])
       (cond 
         [(primitive? op) (apply op args)]
         [(procedure? op) (apply op args)] ; imports 
         [(clos? op)      (handle-clos op)]
         [(case-clos? op) (define n (mlength args))
                          (match-define (case-clos name arities clos-vector) op)
                          ; find the first index for a matching arity
                          (define idx (for/or ([a (in-vector arities)] [i (in-naturals)])
                                        (and (or (and (positive? a) (= a n))
                                                 (and (negative? a) (>= n (- (- a) 1))))
                                             i)))
                          (unless idx (error 'application-of-case-clos "no arities match, got ~a" expr))
                          ; apply the corresponding clos
                          (handle-clos (vector-ref clos-vector idx))]
         [(shell? op) (loop (shell-closure op))]
         [else (error 'call-with-values "can't apply ~a" op)]))]
    [(struct seq (exprs))
     (let loop ([exprs exprs])
       (cond [(null? exprs)        (error 'seq "empty seq")]
             [(null? (rest exprs)) (eval-expr (first exprs))]
             [else                 (eval-expr (first exprs))
                                   (loop (rest exprs))]))]
    [(struct beg0 (exprs))
     (match exprs
       [(list)       (error "beg0: empty form not allowed")]
       [(list expr)  (eval-expr (first exprs))] ; tail position
       [_            (define result (eval-expr/restore (first exprs)))
                     (for ([expr (in-list (rest exprs))])
                       (eval-expr/restore expr))
                     result])]
    [(struct with-cont-mark (key val body))
     (define k (eval-expr/restore key))
     (define v (eval-expr/restore val))
     (with-continuation-mark k v (eval-expr body))]
    [(struct closure (lam gen-id)) 
     ; A lambda form with an empty closure, which is a procedure constant.
     ; (No optimization here, we just allocate a standard closure)
     (eval-expr lam)]
    [(struct varref (tl dummy))
     (error)] ; no #%variable-reference for you
    [else expr])) ; literals evaluate to themselves

;;;
;;; CLOSURES
;;; 

; A closure from a      lambda expression is represented as a      clos structure.
; A closure from a case-lambda expression is represented as a case-clos structure.

(struct clos (name num-params rest? captures body) ; represents a closure at runtime
  ; captures = vector of captured values
  ; body     = code to run in form of zo-form
  #:transparent
  #:property prop:procedure
  ; In most cases we the closure will be applied in eval-expr throuh
  ; the application bytecode. However if call builtin higher order functions 
  ; such as map and apply we need to tell the system to invoke a closure through invoke-clos.
  (λ (op . args) 
    ; the args received were on the real racket stack, but invoke-clos expects
    ; there to (length args) slots on the simulated stack
    (define old-stack stack)
    (define new-slots (make-mlist (length args) '<app>))
    (set! stack (mappend new-slots stack))
    (invoke-clos '<ignored> '<ignored> op args old-stack)))

(struct case-clos (name arities clos-vector) 
  ; represents a closure of a case-lambda 
  ;   clos-vector = vector of clos
  ;   arities = vector of accepted arities  
  ;   The accepted arities are encoded as follows:
  ;    ...
  ;   1 => exactly 1
  ;   0 => exactly 0
  ;  -1 => 0 or more 
  ;  -2 => 1 or more
  ;    ...
  ; See how invoke-case-clos structs are invoked in invoke-case-clos.
  #:transparent
  #:property prop:procedure
  ; Tell system to use invoke-case-clos to invoke closure from case-lambda expressions.
  (λ (op . args) 
    ; the args received were on the real racket stack, but invoke-clos expects
    ; there to (length args) slots on the simulated stack
    (define old-stack stack)
    (define new-slots (make-mlist (length args) '<app>))
    (set! stack (mappend new-slots stack))
    (invoke-case-clos '<ignored> '<ignored> op args old-stack)))


(struct shell (closure) #:transparent #:mutable
  #:property prop:procedure
  ; Tell the system how to invoke let-rec allocated closures
  (λ (op . args)
    ; Remove shell and invoke contents
    (apply (shell-closure op) args)))

(define (invoke-clos rator rands        ; original operator and operands (zo-structs) for debug
                     op args            ; results of evaluating rator and rands (args is a list)
                     old-stack)          ; stack before application
  ; apply a clos
  (match-define (clos name num-params rest? captures body) op)
  ; When the function is called, the rest-argument list (if any) is pushed onto the stack, 
  ; then the normal arguments in reverse order, then the closure-captured values in 
  ; reverse order. Thus, when body is run, the first value on the stack is the first value 
  ; captured by the closure-map array, and so on.
  (define n (length args))
  (cond [(= n num-params)
         ; we didn't bang the operands into the new slots, so we do this (TODO)
         (define margs (list->mlist args))
         (set! stack (mdrop stack n))
         (set! stack (append-vector-to-mlist captures (mappend margs stack)))
         (eval-expr body)]
        [(and (> n num-params) rest?)
         (define-values (normal-args rest) (split-at args num-params))
         ; rest arguments must be a standard list
         (define mnormal-args (list->mlist normal-args))
         (set! stack (append-vector-to-mlist captures 
                                             (mappend mnormal-args (mcons rest old-stack))))
         (eval-expr body)]
        [(> n num-params)
         (error 'app "too many argument applying ~a to ~a" op args)]
        [(< n num-params) 
         (error 'app "too few argument in application\n closure: ~a\n\n arguments: ~a"
                op args)]))

(define (invoke-case-clos rator rands ; original operator and operands (zo-structs)
                          op args     ; results of evaluating rator and rands (args is a list)
                          old-stack)  ; stack before application
  (define n (length args))
  (match-define (case-clos name arities clos-vector) op)
  ; find the first index for a matching arity
  (define idx (for/or ([a (in-vector arities)] [i (in-naturals)])
                (and (or (and (positive? a) (= a n))
                         (and (negative? a) (>= n (- (- a) 1))))
                     i)))
  (unless idx (error 'application-of-case-clos "no arities match, got ~a" expr))
  ; apply the corresponding clos
  (define clos (vector-ref clos-vector idx))
  (invoke-clos rator rands clos args old-stack))

(define (eval-lam expr)
  (match expr
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
     (define captures (make-vector (vector-length closure-map) #f))
     (for ([i (in-naturals)] [pos (in-vector closure-map)])
       ; (displayln (list 'eval-lam "capturing " i " " (mlist-ref stack pos)))
       (vector-set! captures i (mlist-ref stack pos)))
     (clos name num-params rest? captures body)]))

;;;
;;; MODULES
;;; 

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

#;(eval (let ([zo (s-exp->zo '(begin (define x 42) x))])
          `(module m racket/base
             (provide x) 
             (define x #f)
             (set! x 42)     
             ; the evaluation happens inside the module name space
             ;     (variable-reference->namespace (#%variable-reference)) 
             ; evaluates to the namespace "inside" the module
             (parameterize ([current-namespace (variable-reference->namespace (#%variable-reference))])
               (,eval-zo ,zo)))))

(define (eval-module mod-form)
  (match mod-form
    [(struct mod 
       (name        ; symbol          => module name 
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
     (define (provided->provide-spec phase p)
       (match p
         ;(provided sym  mpi/#f   sym     mpi/#f     N      boolean?]
         [(provided name    src src-name  nom-src src-phase protected?)
          (case phase
            [(0)                      name]
            [(1)  `(for-syntax      ,name)]
            [(#f) `(for-label       ,name)]
            [else `(for-meta ,phase ,name)])]))
     (define (provides->provide-form provides)
       `(provide
         ,@(append*
            (for/list ([a (in-list provides)])
              (match-define (list phase vars syntaxs) a)
              (append 
               (for/list ([p (in-list vars)])    (provided->provide-spec    phase    p))
               (for/list ([p (in-list syntaxs)]) (provided->provide-spec (+ phase 1) p)))))))
     (define (provides->var-declarations provides)
       (append*
        (append*
         (for/list ([a (in-list provides)])
           (match-define (list phase vars syntaxs) a)
           (define vs (map provided-name vars))
           (case phase
             [(0) `((define-values ,vs (values ,@(for/list ([v vs]) ''undef-decl))))]
             [else '()])))))
     
     ; (displayln (list 'eval-module provides))
     ; (displayln (list 'eval-module (provides->provide-form provides)))
     ; (displayln (list 'eval-module (provides->var-declarations provides)))
     
     ; provides = ((0 (#s((provided zo 0) x #f x #f 0 #f)) ())   ; phase 0
     ;             (1 () ())                                     ; phase 1
     ;             (#f () ())))                                  ; phase label
     ; association list  (phase <list-of-provided-variables> <list-of-provided-syntax>)
     ; (error)
     (define mod-sexp
       `(module ,srcname racket/base ; keep racket/base for now
          ,(provides->provide-form provides)
          ,(provides->var-declarations provides)     
          ; the evaluation happens inside the module name space
          ;     (variable-reference->namespace (#%variable-reference)) 
          ; evaluates to the namespace "inside" the module
          (displayln ,(~a "instantiating module: " srcname))
          (parameterize ([current-namespace (variable-reference->namespace (#%variable-reference))]
                         [compile-allow-set!-undefined #t])
            ; evaluate body 
            (,eval-form ,(trace (module-body prefix body))))))
     ; (write (list 'module: mod-sexp)) (newline)
     (parameterize (#;[current-module-declare-name (make-resolved-module-path srcname)]
                    [compile-enforce-module-constants #f]
                    #;[compile-allow-set!-undefined #t])
       (eval mod-sexp))]
    [else (error 'decompile-module "huh?: ~e" mod-form)]))

;;;
;;; TESTS
;;;
;; ----------------------------------------
(define verbose displayln)
(require rackunit)
(verbose "Running test programs")

(verbose "program1")
(define program1 (string->zo (~a 42)))           ; literal
(check-equal? (eval-zo program1) 42)

(define program2 (string->zo (~a 'time-apply)))  ; primval
(check-equal? (eval-zo program2) time-apply)

(define program3 (string->zo (~a '(time-apply void '()))))  ; application of primitives
(check-equal? (let-values ([(val _ __ ___) (eval-zo program3)]) val) (list (void)))

(define program4 ; application of closure and localref
  (string->zo (~a '(let () (define (foo x) x) (foo 43))))) 
(check-equal? (eval-zo program4) 43)

(define program5 ; check the order in which arguments are pushed to the stack:
  (string->zo (~a '(let () (define (foo x y) (list x y)) (foo 41 42))))) 
(check-equal? (eval-zo program5) (list 41 42))



(verbose "program6")
(define program6 ; check rest arguments
  (string->zo (~a '(let()(define (foo x y . z) (list (+ x y) z)) (foo 41 42 43 44)))))
(check-equal? (eval-zo program6) '(83 (43 44)))

(verbose "program7")
(define program7 (string->zo (~a '(let() (define (foo x) (set! x (+ x 1)) x) (foo 41)))))
(check-equal? (eval-zo program7) 42)

(define program8 (string->zo 
                  (~a '(let() (define (foo x y z) (set! y (+ x y z)) (list x y z)) (foo 41 42 43)))))
(check-equal? (eval-zo program8) '(41 126 43))

(define program9 ; let-one
  (string->zo (~a '(let() (define-values (a b c) (values 41 42 43)) (set! b 44) (list a b c)))))
(check-equal? (eval-zo program9) '(41 44 43))

(verbose "program10")
(define program10 ; branch
  (string->zo (~a '(let() (define (fact n) (if (zero? n) 1 (* n (fact (- n 1))))) (fact 5)))))

; test module-variable in prefix  (build-list is imported form racket/list via racket/base)
(define program11 (string->zo (~a '(let () (build-list 3 values)))))
(check-equal? (eval-zo program11) '(0 1 2))

(define program12 ; beg0
  (string->zo (~a '(let () (define (foo x) x) (begin0 (foo 42) 43)))))
(check-equal? (eval-zo program12) 42)

(define program13 ; with-continuation-mark
  (string->zo (~a '(let ()
                     (define (extract-current-continuation-marks key)
                       (continuation-mark-set->list (current-continuation-marks) key))
                     (with-continuation-mark 'key 'mark 
                       (extract-current-continuation-marks 'key))))))
(check-equal? (eval-zo program13) '(mark))

(define program14 ; seq
  (string->zo (~a '(let () (define (foo x) x) (+ (begin (foo 41) 42) 43)))))
(check-equal? (eval-zo program14) 85)

(verbose "program15")
(define program15 ; call-with-values
  (string->zo (~a '(let () (define (foo x) x) (call-with-values (λ() (values (foo 42) 43)) list)))))
(check-equal? (eval-zo program15) '(42 43))

(define program16 ; case-lambda
  (string->zo  
   (~a '(let () (define foo (case-lambda [(x) 41] [(x y) 42])) (list (foo 51) (foo 52 53))))))
(check-equal? (eval-zo program16) '(41 42))

(define program17 ; case-lambda
  (string->zo  
   (~a '(let () (define foo (case-lambda [(x . z) 41] [(x y) 42])) (list (foo 51) (foo 52 53))))))
(check-equal? (eval-zo program17) '(41 41))

(define program18 ; call-with-values with a case-lambda
  (string->zo (~a '(let () 
                     (define (foo x) x)
                     (define bar (case-lambda [(x) 41] [(x y) 42]))
                     (call-with-values (λ() (values (foo 51) 52)) bar)))))
(check-equal? (eval-zo program18) 42)

(define program19 ; call-with-values with a case-lambda
  (string->zo (~a '(let () 
                     (define (foo x) x)
                     (define bar (case-lambda [(x . z) 41] [(x y) 42]))
                     (call-with-values (λ() (values (foo 51) 52)) bar)))))
(check-equal? (eval-zo program19) 41)

(verbose "program20")
(define program20 ; let-void and variable capture
  (string->zo 
   (~a '(letrec ([foo (lambda (x) (if (zero? x) 41 (if (even? x) (bar x) (foo (- x 1)))))]
                 [bar (lambda (x) (if (zero? x) 42 (if (even? x) (foo (- x 1)) (bar (- x 1)))))]
                 [baz (lambda () (set! foo 43))]
                 )
          (foo 2)))))
(check-equal? (eval-zo program20) 41)

(define program21 ; let-rec
  (compile-zo '(letrec ([p (lambda (x) (+ 1 (q (- x 1))))] 
                       [q (lambda (y) (if (zero? y) 0 (+ 1 (p (- y 1)))))]
                       [x (p 5)]
                       [y x])
                y)))
(check-equal? (eval-zo program21) 5)

(define program22 ; assign and the form seq
  (compile-zo '(let () (set! first first) first)))
(check-equal? (eval-zo program22) first)

(define program23 ; top-level define-values
  (compile-zo '(begin (define x 42) x)))
(check-equal? (eval-zo program23) 42)

(define program24 ; topsyntax and stx in prefix
  (compile-zo '#'42))
; Hmm. (equal? #'42 #'42) is #f, so check-equal? is not helpful here
; (check-equal? (eval-zo program24)  (racket-eval-zo program24))
(check-equal? (syntax->datum (eval-zo program24)) 42)

(define program25 ; toplevel require
  (compile-zo '(begin (require racket/port) port->list)))
; (check-equal? (eval-zo program25) port->list) ; works but are not equal? ???

; Are lambda, case-lambe and let-rec producing closures?
(define program26a '(let ([x 41]) (λ (y) (list x y))))
(define program26b '(let ([x 41]) (case-lambda [(y) (list x y)] [(y z) (list x y z)])))
(define program26c '(letrec ([even? (lambda (x) (if (zero? x) #t (odd? (- x 1))))]
                             [odd?  (lambda (x) (if (zero? x) #f (even? (- x 1))))])
                      even?))
(check-true (clos?      (eval-zo program26a)))
(check-true (case-clos? (eval-zo program26b)))
(check-true (shell?     (eval-zo program26c)))
; Check that closures can be invoked by Racket procedures.
(check-equal? ((eval-zo program26a) 42)    '(41 42))
(check-equal? ((eval-zo program26b) 42)    '(41 42))
(check-equal? ((eval-zo program26b) 42 43) '(41 42 43))
(check-true   ((eval-zo program26c) 4))
(check-false  ((eval-zo program26c) 5))
; And by the interpreter
(check-equal? (eval-zo `(,program26a 42))    '(41 42))
(check-equal? (eval-zo `(,program26b 42))    '(41 42))
(check-equal? (eval-zo `(,program26b 42 43)) '(41 42 43))
(check-true   (eval-zo `(,program26c 4)))
(check-false  (eval-zo `(,program26c 5)))

(use-current)
(define program27 ; seq-for-syntax
  '(begin (define x 40) (begin-for-syntax (define x 41)) x))
(parameterize ([current-namespace (variable-reference->namespace (#%variable-reference))])
  (check-equal? (eval-zo program27) 40))


(use-current)
(parameterize ([current-namespace (variable-reference->namespace (#%variable-reference))])
; (with-start-namespace (dynamic-require-for-syntax 'racket/base 0)
  (check-equal? (eval-zo '(begin (define x 1) 
                                 (define-syntax (y _) #'x)
                                 x))
                1))

(use-start)
;;;
;;; FROM THE R6RS TEST SUITE
;;;

(require (for-syntax syntax/parse racket/base))
(define test-program 'none)
(define test-zo 'none)

; (define-syntax (test stx) #'(void)) ; for disabling tests

(define-syntax (test stx)
  (syntax-parse stx
    [(_ s-exp expected)
     (with-syntax ([t   (datum->syntax #'stx 'test                    #'s-exp)]
                   [loc (datum->syntax #'stx (syntax->datum #''s-exp) #'s-exp)])
       #`(begin
           (set! test-zo 'none)
           (set! test-program 's-exp)
           (define zo (compile-zo 's-exp))
           (set! test-zo zo)
           (define actual (eval-zo zo))
           (unless (equal? actual expected)
             (raise-syntax-error 'test 
                                 (~a "test failed\n expected: " expected "\n actual: " actual "\n")
                                 #'s-exp))))]))
(test 42 42)
; (test (+ 1 2) 4)

;; Expressions ----------------------------------------
;;; Test-suite from: http://svn.plt-scheme.org/plt/trunk/collects/tests/r6rs/base.sls

(verbose "11.2.1")
;(test (add3 3) 6)
(test (first '(1 2)) 1)

(verbose "11.2.2")
(test (let ()
        (define even?
          (lambda (x)
            (or (= x 0) (odd? (- x 1)))))
        (define-syntax odd?
          (syntax-rules ()
            ((odd?  x) (not (even? x)))))
        (even? 10))
      #t)
(test (let ()
        (define-syntax bind-to-zero
          (syntax-rules ()
            ((bind-to-zero id) (define id 0))))
        (bind-to-zero x)
        x)
      0)

(verbose "11.3")
(test (let ((x 5))
        (define foo (lambda (y) (bar x y)))
        (define bar (lambda (a b) (+ (* a b) a)))
        (foo (+ x 3)))
      45)
(test (let ((x 5))
        (letrec ((foo (lambda (y) (bar x y)))
                 (bar (lambda (a b) (+ (* a b) a))))
          (foo (+ x 3))))
      45)

#;(test/exn (letrec ([x y]
                     [y x])
              'should-not-get-here)
            &assertion)

(test (letrec ([x (if (eq? (cons 1 2) (cons 1 2))
                      x
                      1)]) 
        x)
      1)

(verbose "11.4.1")
;; (These tests are especially silly, since they really
;;  have to work to get this far.)
(test (quote a) 'a)
(test (quote #(a b c)) (vector 'a 'b 'c))
(test (quote (+ 1 2)) '(+ 1 2))
(test '"abc" "abc")
(test '145932 145932)
(test 'a 'a)
(test '#(a b c) (vector 'a 'b 'c))
(test '() (list))
(test '(+ 1 2) '(+ 1 2))
(test '(quote a) '(quote a))
(test ''a '(quote a))

(verbose "11.4.2")
;; (test (lambda (x) (+ x x)) {a procedure})
(test ((lambda (x) (+ x x)) 4) 8)
(test ((lambda (x)
         (define (p y)
           (+ y 1))
         (+ (p x) x))
       5) 
      11)
;(test (reverse-subtract 7 10) 3)
;(test (add4 6) 10)
(test ((lambda x x) 3 4 5 6) '(3 4 5 6))
(test ((lambda (x y . z) z) 3 4 5 6)
      '(5 6))

(verbose "11.4.3")
(test (if (> 3 2) 'yes 'no) 'yes)
(test (if (> 2 3) 'yes 'no) 'no)
(test (if (> 3 2)
          (- 3 2)
          (+ 3 2))
      1)
;(test/unspec (if #f #f))

(verbose "11.4.4")
(test (let ((x 2))
        (+ x 1)
        (set! x 4)
        (+ x 1)) 
      5)

(verbose "11.4.5")
(test (cond ((> 3 2) 'greater)
            ((< 3 2) 'less))          
      'greater)

(test (cond ((> 3 3) 'greater)
            ((< 3 3) 'less)
            (else 'equal))
      'equal)
(test (cond ('(1 2 3) => cadr)
            (else #t))          
      2)

(test (case (* 2 3)
        ((2 3 5 7) 'prime)
        ((1 4 6 8 9) 'composite))
      'composite)
#;(test/unspec (case (car '(c d))
                 ((a) 'a)
                 ((b) 'b)))
(test (case (car '(c d))
        ((a e i o u) 'vowel)
        ((w y) 'semivowel)
        (else 'consonant))
      'consonant)

(test (and (= 2 2) (> 2 1)) #t)
(test (and (= 2 2) (< 2 1)) #f)
(test (and 1 2 'c '(f g)) '(f g))
(test (and) #t)

(test (or (= 2 2) (> 2 1)) #t)
(test (or (= 2 2) (< 2 1)) #t)
(test (or #f #f #f) #f)
(test (or '(b c) (/ 3 0)) '(b c))

(verbose "11.4.6")
(test (let ((x 2) (y 3)) (* x y)) 6)
(test (let ((x 2) (y 3)) (let ((x 7) (z (+ x y))) (* z x))) 35)
(test (let ((x 2) (y 3)) (let* ((x 7) (z (+ x y))) (* z x))) 70)
(test (letrec ((even?
                (lambda (n)
                  (if (zero? n)
                      #t
                      (odd? (- n 1)))))
               (odd?
                (lambda (n)
                  (if (zero? n)
                      #f
                      (even? (- n 1))))))
        (even? 88))   
      #t)
(test (letrec ((p                               ; was letrec*
                (lambda (x)
                  (+ 1 (q (- x 1)))))
               (q
                (lambda (y)
                  (if (zero? y)
                      0
                      (+ 1 (p (- y 1))))))
               (x (p 5))
               (y x))
        y)
      5)
(test (let-values (((a b) (values 1 2))
                   ((c d) (values 3 4)))
        (list a b c d))
      '(1 2 3 4))
#;(test (let-values (((a b . c) (values 1 2 3 4))) ; let-values with rest args not in Racket
          (list a b c))
        '(1 2 (3 4)))
(test (let ((a 'a) (b 'b) (x 'x) (y 'y))
        (let-values (((a b) (values x y))
                     ((x y) (values a b)))
          (list a b x y)))
      '(x y a b))
(test (let ((a 'a) (b 'b) (x 'x) (y 'y))
        (let*-values (((a b) (values x y))
                      ((x y) (values a b)))
          (list a b x y)))
      '(x y x y))

(verbose "11.6")
(test (procedure? car) #t)
(test (procedure? 'car) #f)
(test (procedure? (lambda (x) (* x x))) #t)
(test (procedure? '(lambda (x) (* x x))) #f)

(test (call-with-values * -) -1)

(verbose "11.16")
(test (let loop ((numbers '(3 -2 1 6 -5))
                 (nonneg '())
                 (neg '()))
        (cond ((null? numbers) (list nonneg neg))
              ((>= (car numbers) 0)
               (loop (cdr numbers)
                     (cons (car numbers) nonneg)
                     neg))
              ((< (car numbers) 0)
               (loop (cdr numbers)
                     nonneg
                     (cons (car numbers) neg)))))
      '((6 1 3) (-5 -2)))

(use-current)

(current-namespace (variable-reference->namespace (#%variable-reference)))

#;(begin ; works but noisy
  (verbose "module1")
  (use-current)
  (with-start-namespace
      (eval-zo (compile-zo '(module m racket/base (provide x)              (displayln "-- m --") (define x 42) x)))
    (eval-zo (compile-zo '(require 'm)))
    (eval-zo (compile-zo '(module n racket/base (require 'm) (provide y) (displayln "-- n --") (define y x) y)))
    (eval-zo (compile-zo '(require 'n)))))

#;(begin ; Works - but noisy
  (verbose "module2")
  (with-start-namespace
      (eval-zo (compile-zo '(module m racket/base 
                             (provide x y)
                             (displayln "-- m --")
                             (define x 40)
                             (define y (+ x 1))
                             (list x y))))
    (eval-zo (compile-zo '(require 'm)))
    (eval-zo (compile-zo '(module n racket/base 
                           (require 'm)
                           (provide z) 
                           (displayln "-- n --")
                           (define z (list x y))
                           z)))
    (eval-zo (compile-zo '(require 'n)))))


;;;
;;; WELCOME
;;; 

(use-start)
; (use-current)

(displayln "Welcome to the Meta Racket VM")
(displayln (~a "Mode: 'start  (which means make-start-namespace is used as default)"))
; (displayln (~a "Mode: 'current  (which means (current-namespace) is used as default)"))
(displayln "Use (use-curent) to use (current-namespace) as default")
(displayln "Use (use-start)  to use (make-start-namespace) as default")
(newline)
(displayln "(eval-zo    s-expr) : evaluate s-expression")
(displayln "(expand-zo  s-expr) : expand s-expression")
(displayln "(compile-zo s-expr) : compile s-expression to zo bytecode")
(newline)
(displayln "In (use-current) mode the compiler use the current-environment.")
(displayln "When used in DrRacket it means that the language settings effect,")
(displayln "the bytecodes produced by the compiler. You might want to disable ")
(displayln "debugging and stack tracing to get sensible bytecodes.")
(displayln "In (use-start) mode the environment is controlled, but definitions")
(displayln "made in the repl won't be picked up.")
(newline)

(displayln "Happy Rackeetering! -- Jens Axel (jensaxel@soegaard.net)")


