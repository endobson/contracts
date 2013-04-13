#lang racket/base

(require "structures.rkt" racket/list
         racket/match
         (for-syntax racket/base racket/syntax syntax/parse))

;; for syntax
(require racket/set
         unstable/contract
         (except-in racket/contract recursive-contract))

(provide (all-defined-out))

;;Printing
(define (any-write-proc v port mode)
  (if (equal? mode 0)
      (display "any/sc" port)
      (display "#<any/sc>" port)))


;; Helpers
(define ((app stx) . ctcs) #`(#,stx #,@ctcs))

(define ((combine combinator stx) sc)
  (combinator (app stx) (list sc)))
(define ((combine* combinator stx) scs)
  (combinator (app stx) scs))

(define ((combinator-map* constructor) v f)
  (match v
    [(combinator stx args) (constructor stx (for/list ((a args))
                                              (f a 'pos)))]))
(define-syntax-rule (combinator-map constructor)
  (combinator-map* (lambda (stx args) (constructor stx args))))

(begin-for-syntax
  (define-syntax-class variance-keyword
    #:attributes (variance)
    [pattern (~and kw (~or #:covariant #:contravariant #:invariant))
             #:attr variance (string->symbol (keyword->string (syntax-e (attribute kw))))])
  (define-syntax-class contract-category-keyword
    #:attributes (category struct)
    [pattern (~and kw (~or #:flat #:chaperone #:impersonator))
             #:attr category (string->symbol (keyword->string (syntax-e (attribute kw))))
             #:attr struct (case (attribute category)
                             ((flat) #'flat-combinator)
                             ((chaperone) #'chaperone-combinator)
                             ((impersonator) #'impersonator-combinator))])

  (define-syntax-class argument-description
    #:attributes (variance name restricted-name)
    [pattern ((~or (~optional :contract-category-keyword)
                   (~once :variance-keyword)) ...)
             #:attr name (generate-temporary)
             #:attr restricted-name
               (case (attribute category)
                 ((flat) #'(flat-restrict name))
                 ((chaperone) #'(chaperone-restrict name))
                 (else #'name))])

  (define-syntax-class static-combinator-form
    #:attributes (name combinator matcher)
    [pattern (name:id pos:argument-description ... )
             #:with matcher-name (format-id #'name "~a:" (syntax-e #'name))
             #:attr combinator
               #'(λ (constructor ctc) (λ (pos.name ...) (constructor (app ctc) (list pos.restricted-name ...))))
             #:attr matcher
               (λ (struct-name)
                 #`(define-match-expander matcher-name
                     (syntax-parser
                       [(_ pos.name ...)
                        #'(#,struct-name _ (list pos.name ...))])))]
    [pattern (name:id . rest:argument-description)
             #:with matcher-name (format-id #'name "~a:" (syntax-e #'name))
             #:attr combinator
               #'(λ (constructor ctc) (λ args (constructor (app ctc) args)))
             #:attr matcher
               (λ (struct-name)
                 #`(define-match-expander matcher-name
                     (syntax-parser
                      [(_ ctc (... ...))
                       #'(#,struct-name _ (list ctc (... ...)))])))]))



(define-syntax (combinator-struct stx)
  (syntax-parse stx
    [(_ sc:static-combinator-form c:expr kind:contract-category-keyword)
     #`(begin
         (struct struct-name kind.struct ()
                 #:methods gen:sc-mapable [(define sc-map (combinator-map struct-name))]
                 #:property prop:combinator-name (symbol->string 'sc.name))
         #,((attribute sc.matcher) #'struct-name)
         (define sc.name (sc.combinator struct-name c)))]))


(define-syntax (combinator-structs stx)
  (syntax-parse stx
    [(_ (e ...) ...)
     #`(begin
         (combinator-struct e ...) ...)]))

(combinator-structs
  ((or/sc . (#:covariant)) or/c #:flat)
  ((and/sc . (#:covariant)) and/c #:flat)
  ((list/sc . (#:covariant)) list/c #:flat)
  ((listof/sc (#:covariant)) listof #:flat)
  ((cons/sc (#:covariant) (#:covariant)) cons/c #:flat)
  ;; TODO add chaperone restrict
  ((set/sc (#:covariant #:chaperone)) set/c #:flat)
  ((vector/sc . (#:invariant)) vector/c #:chaperone)
  ((vectorof/sc (#:invariant)) vectorof #:chaperone)
  ((promise/sc (#:covariant)) promise/c #:chaperone)
  ((syntax/sc (#:covariant #:flat)) syntax/c #:flat)
  ((hash/sc (#:invariant #:flat) (#:invariant)) hash/c #:chaperone)
  ((box/sc (#:invariant)) box/c #:chaperone)
  ((parameter/sc (#:contravariant) (#:covariant)) parameter/c #:chaperone)
  ((sequence/sc (#:covariant)) sequence/c #:chaperone))


;; Struct Definitions
(struct any-combinator simple-contract ()
        #:methods gen:custom-write [(define write-proc any-write-proc)])
(struct struct-combinator chaperone-combinator ())
(struct continuation-mark-key-combinator chaperone-combinator ())
(struct prompt-tag-combinator chaperone-combinator ())
(struct parametric-combinator flat-combinator ())
(struct function-combinator chaperone-combinator ())
(struct case->-combinator chaperone-combinator ())
(struct arr-combinator chaperone-combinator ())


;; Combinators
(define (flat/sc ctc) (simple-contract ctc 'flat))
(define (chaperone/sc ctc) (simple-contract ctc 'chaperone))
(define (impersonator/sc ctc) (simple-contract ctc 'impersonator))

(define continuation-mark-key/sc
  (combine continuation-mark-key-combinator #'continuation-mark-key/c))

(define (prompt-tag/sc* scs call/cc-sc)
  (prompt-tag-combinator
    (λ (call/cc-ctc . others)
       #`(prompt-tag/c #,@others #:call/cc call/cc-ctc)
       (cons call/cc-sc scs))))

(define (object/sc* methods) (error 'nyi))
(define (class/sc* methods) (error 'nyi))


(define any/sc (any-combinator #'any/c 'flat))
(define identifier/sc (flat/sc #'identifier?))

(define (function/sc mand-args opt-args mand-kws opt-kws rest range)
  (define mand-args-start 0)
  (define mand-args-end (length mand-args))
  (define opt-args-start mand-args-end)
  (define opt-args-end (+ opt-args-start (length opt-args)))
  (define mand-kw-args-start opt-args-end)
  (define mand-kw-args-end (+ mand-kw-args-start (length mand-kws)))
  (define opt-kw-args-start mand-kw-args-end)
  (define opt-kw-args-end (+ opt-kw-args-start (length opt-kws)))
  (define rest-start opt-kw-args-end)
  (define rest-end (if rest (add1 rest-start) rest-start))
  (define range-start rest-end)
  (define range-end (if range (+ range-start (length range)) range-start))
  (function-combinator
    (lambda ctcs
      (define mand-ctcs (drop (take ctcs mand-args-end) mand-args-start))
      (define opt-ctcs (drop (take ctcs opt-args-end) opt-args-start))
      (define mand-kw-ctcs (drop (take ctcs mand-kw-args-end) mand-kw-args-start))
      (define opt-kw-ctcs (drop (take ctcs opt-kw-args-end) opt-kw-args-start))
      (define rest-ctc-stx
        (if rest
            (list '#:rest (first (drop (take ctcs rest-end) rest-start)))
            #'()))
      (define range-ctc
        (if range
            #`(values #,@(drop (take ctcs range-end) range-start))
            #'any))

      (define mand-kws-stx (append-map list (map first mand-kws) mand-kw-ctcs))
      (define opt-kws-stx (append-map list (map first opt-kws) opt-kw-ctcs))


      #`((#,@mand-ctcs #,@mand-kws-stx)
         (#,@opt-ctcs #,@opt-kws-stx) 
         #,@rest-ctc-stx
         . ->* . #,range-ctc))
    (append
      mand-args
      opt-args
      (map second mand-kws)
      (map second opt-kws)
      (if rest (list rest) null)
      (or range null))))

(define case->/sc 
  (combine* case->-combinator #'case->))

(define (arr/sc mand-args rest range)
  (define mand-args-start 0)
  (define mand-args-end (length mand-args))
  (define rest-start mand-args-end)
  (define rest-end (if rest (add1 rest-start) rest-start))
  (define range-start rest-end)
  (define range-end (if range (+ range-start (length range)) range-start))
  (arr-combinator
    (lambda ctcs
      (define mand-ctcs (drop (take ctcs mand-args-end) mand-args-start))
      (define rest-ctc-stx
        (if rest
            (list '#:rest (first (drop (take ctcs rest-end) rest-start)))
            #'()))
      (define range-ctc
        (if range
            #`(values #,@(drop (take ctcs range-end) range-start))
            #'any))
      #`(#,@mand-ctcs #,@rest-ctc-stx . -> . #,range-ctc))
    (append
      mand-args
      (if rest (list rest) null)
      (or range null))))

(define (struct/sc name fields)
  (struct-combinator (λ ctcs #`(struct/c name #,ctcs)) fields))

(define (parametric->/sc vars body)
  (parametric-combinator (λ (ctc) #`(parametric->/c (#,@vars) #,ctc)) body))



(define-match-expander any/sc:
  (syntax-parser
    [(_) #'(any-combinator _ _)]))


